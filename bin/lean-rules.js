#!/usr/bin/env node
// lean-rules - declarative Lean 4 lint-rule runner.
//
// Loads YAML rule files (the pi-lens rule schema: id, language, severity,
// message, note, rule = {regex} | {any: [...]} | {all: [...]}) and scans
// Lean sources for violations. Composite conditions nest recursively:
//   any = at least one child matches; all = every child matches.
// Rust-regex inline flags ((?m), (?i), (?s)) are translated to JS flags;
// a rule whose pattern cannot compile in JS is reported as a
// RULE_COMPILE_WARNING, never a crash.
//
// Usage:
//   lean-rules [files-or-dirs...] [--rules <dir>]... [--config lean-project.toml] [--json] [--min-severity warning|error]
//   (with no positional targets, scans the current directory recursively
//    for *.lean)
// Exit codes: 0 = no findings at or above the severity floor, 1 = findings,
// 2 = usage error.

import fs from "node:fs";
import path from "node:path";
import yaml from "js-yaml";
import { parseToml, findConfig, checkArchitecture } from "./lean-architecture.mjs";

const SEVERITY_ORDER = { hint: 0, info: 1, warning: 2, error: 3 };

function parseArgs(argv) {
  const opts = { targets: [], rulesDirs: [], json: false, minSeverity: "warning" };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--rules") opts.rulesDirs.push(argv[++i]);
    else if (a === "--config") opts.config = argv[++i];
    else if (a === "--json") opts.json = true;
    else if (a === "--min-severity") opts.minSeverity = argv[++i];
    else if (a === "--help" || a === "-h") {
      console.log("usage: lean-rules [files-or-dirs...] [--rules <dir>]... [--config lean-project.toml] [--json] [--min-severity warning|error]");
      process.exit(0);
    } else opts.targets.push(a);
  }
  if (!(opts.minSeverity in SEVERITY_ORDER)) {
    console.error(`unknown severity: ${opts.minSeverity}`);
    process.exit(2);
  }
  return opts;
}

function toJsRegex(pattern) {
  // Multiline is the DEFAULT (the host scanner applies line-anchored
  // semantics to every rule; some corpus patterns rely on it without
  // carrying an inline (?m)). Inline flags are stripped and folded into
  // the JS flag set.
  let flags = "gm";
  let p = pattern;
  if (p.includes("(?m)")) p = p.replaceAll("(?m)", "");
  if (p.includes("(?i)")) { flags += "i"; p = p.replaceAll("(?i)", ""); }
  if (p.includes("(?s)")) { flags += "s"; p = p.replaceAll("(?s)", ""); }
  return new RegExp(p, flags);
}

// Lean-aware mask: replace comments and string literals with spaces while
// preserving every newline, so line/column arithmetic on the masked text is
// identical to the raw source. An audit gate that cannot tell prose from code
// is unsound in both directions: it flags a comment that SAYS "no sorry" and it
// green-lights a proof whose only remaining `sorry` sits inside a docstring.
// Rules therefore match against masked code by default; a rule that really
// targets prose opts in with `scope: any`.
export function maskLeanNonCode(text) {
  const out = text.split("");
  const blank = (i) => { if (out[i] !== "\n") out[i] = " "; };
  let i = 0;
  const n = text.length;
  while (i < n) {
    const ch = text[i];
    const next = text[i + 1];
    // line comment
    if (ch === "-" && next === "-") {
      while (i < n && text[i] !== "\n") { blank(i); i++; }
      continue;
    }
    // block comment, Lean nests them
    if (ch === "/" && next === "-") {
      let depth = 0;
      while (i < n) {
        if (text[i] === "/" && text[i + 1] === "-") { depth++; blank(i); blank(i + 1); i += 2; continue; }
        if (text[i] === "-" && text[i + 1] === "/") { depth--; blank(i); blank(i + 1); i += 2; if (depth === 0) break; continue; }
        blank(i); i++;
      }
      continue;
    }
    // string literal
    if (ch === '"') {
      blank(i); i++;
      while (i < n) {
        if (text[i] === "\\") { blank(i); blank(i + 1); i += 2; continue; }
        if (text[i] === '"') { blank(i); i++; break; }
        if (text[i] === "\n") { i++; break; } // unterminated: do not swallow the file
        blank(i); i++;
      }
      continue;
    }
    i++;
  }
  return out.join("");
}

// Evaluate a rule node against the content. Returns the matching pattern
// strings or null when the node does not match. A regex node matches only if
// the compiled pattern actually MATCHES the content (compile success is not
// a match). Regexes carry the g flag, so lastIndex is reset before every test.
function evalNode(node, content, compiled) {
  if (typeof node === "string") {
    const re = compiled(node);
    if (!re) return null;
    re.lastIndex = 0;
    return re.test(content) ? [node] : null;
  }
  if (node.regex !== undefined) {
    const re = compiled(node.regex);
    if (!re) return null;
    re.lastIndex = 0;
    return re.test(content) ? [node.regex] : null;
  }
  if (Array.isArray(node.any)) {
    for (const child of node.any) {
      const r = evalNode(child, content, compiled);
      if (r) return r;
    }
    return null;
  }
  if (Array.isArray(node.all)) {
    const hits = [];
    for (const child of node.all) {
      const r = evalNode(child, content, compiled);
      if (!r) return null;
      hits.push(...r);
    }
    return hits;
  }
  return null;
}

function loadRules(rulesDir) {
  const rules = [];
  const warnings = [];
  for (const entry of fs.readdirSync(rulesDir).sort()) {
    if (!entry.endsWith(".yml") && !entry.endsWith(".yaml")) continue;
    const full = path.join(rulesDir, entry);
    let doc;
    try {
      doc = yaml.load(fs.readFileSync(full, "utf-8"));
    } catch (e) {
      warnings.push({ rule: entry, reason: `yaml parse: ${e.message}` });
      continue;
    }
    if (!doc || doc.language !== "Lean" || !doc.id || !doc.rule) continue;
    rules.push({ file: entry, ...doc });
  }
  return { rules, warnings };
}

function walkLean(targets) {
  const files = [];
  const visit = (p) => {
    const st = fs.statSync(p);
    if (st.isDirectory()) {
      for (const e of fs.readdirSync(p).sort()) {
        if (e === "node_modules" || e === ".git" || e === "dist" || e === ".lake" || e === "build") continue;
        visit(path.join(p, e));
      }
    } else if (p.endsWith(".lean") || targets.includes(p)) {
      // Explicit file targets are scanned whatever the extension (lint
      // fixtures may deliberately carry broken Lean and a non-.lean name
      // so editors and LSPs never elaborate them).
      files.push(p);
    }
  };
  for (const t of targets) visit(t);
  return files;
}

export function runScan({ rulesDir, rulesDirs, targets, minSeverity = "warning", config = null }) {
  const dirs = rulesDirs ?? (rulesDir ? [rulesDir] : []);
  const rules = [];
  const warnings = [];
  for (const d of dirs) {
    const r = loadRules(d);
    rules.push(...r.rules);
    warnings.push(...r.warnings);
  }
  const cfgPath = config ?? findConfig(targets[0] ?? ".");
  const cfg = cfgPath ? parseToml(fs.readFileSync(cfgPath, "utf-8")) : null;
  const cfgDir = cfgPath ? path.dirname(cfgPath) : ".";
  if (cfg) for (const d of cfg.rules?.extra_dirs ?? []) {
    const full = path.resolve(cfgDir, d);
    if (fs.existsSync(full)) { const r = loadRules(full); rules.push(...r.rules); warnings.push(...r.warnings); }
  }
  const compileCache = new Map();
  const compiled = (pattern) => {
    if (!compileCache.has(pattern)) {
      try { compileCache.set(pattern, toJsRegex(pattern)); }
      catch { compileCache.set(pattern, null); }
    }
    return compileCache.get(pattern);
  };
  const compileWarnRules = [];
  const findings = [];
  const files = walkLean(targets);
  for (const file of files) {
    const content = fs.readFileSync(file, "utf-8");
    // `scope: any` opts a rule into raw text (prose rules); default is code.
    const codeContent = maskLeanNonCode(content);
    if (cfg) {
      const floor = SEVERITY_ORDER[minSeverity] ?? 2;
      for (const f of checkArchitecture(file, content, codeContent, cfg, cfgDir)) {
        if ((SEVERITY_ORDER[f.severity] ?? 2) >= floor) findings.push({ file, ...f });
      }
    }
    for (const rule of rules) {
      const haystack = rule.scope === "any" ? content : codeContent;
      let matched = null;
      try {
        matched = evalNode(rule.rule, haystack, compiled);
      } catch (e) {
        warnings.push({ rule: rule.id, reason: `eval: ${e.message}` });
        continue;
      }
      if (!matched) continue;
      const floor = SEVERITY_ORDER[minSeverity] ?? 2;
      if ((SEVERITY_ORDER[rule.severity] ?? 2) < floor) continue;
      // First match position -> line number.
      let line = 1;
      const firstPattern = Array.isArray(matched) ? matched[0] : null;
      const re = typeof firstPattern === "string" ? compiled(firstPattern) : null;
      if (re) {
        re.lastIndex = 0;
        const m = re.exec(haystack);
        if (m) line = haystack.slice(0, m.index).split("\n").length;
      }
      findings.push({
        file,
        line,
        ruleId: rule.id,
        severity: rule.severity,
        message: typeof rule.message === "string" ? rule.message : (rule.message?.trim?.() ?? rule.id),
      });
    }
  }
  for (const r of rules) {
    if (JSON.stringify(r.rule).includes("regex") && !evalNode(r.rule, "", () => false)) {
      // compile check: any regex that fails toJsRegex lands here lazily;
      // report rules whose every regex failed to compile
      const patterns = [];
      const collect = (n) => {
        if (typeof n === "string") patterns.push(n);
        else if (n?.regex !== undefined) patterns.push(n.regex);
        for (const k of ["any", "all"]) if (Array.isArray(n?.[k])) n[k].forEach(collect);
      };
      collect(r.rule);
      if (patterns.length > 0 && patterns.every((p) => compiled(p) === null)) {
        compileWarnRules.push(r.id);
      }
    }
  }
  findings.sort((a, b) => a.file.localeCompare(b.file) || a.line - b.line || a.ruleId.localeCompare(b.ruleId));
  return { findings, warnings, compileWarnRules, ruleCount: rules.length, fileCount: files.length };
}

function main() {
  const opts = parseArgs(process.argv.slice(2));
  const rulesDirs = opts.rulesDirs.length > 0 ? opts.rulesDirs : [path.join(path.dirname(new URL(import.meta.url).pathname), "..", "rules")];
  for (const rulesDir of rulesDirs) if (!fs.existsSync(rulesDir)) {
    console.error(`rules directory not found: ${rulesDir}`);
    process.exit(2);
  }
  const targets = opts.targets.length > 0 ? opts.targets : ["."];
  for (const t of targets) {
    if (!fs.existsSync(t)) {
      console.error(`target not found: ${t}`);
      process.exit(2);
    }
  }
  const { findings, warnings, compileWarnRules, ruleCount, fileCount } = runScan({
    rulesDirs, targets, minSeverity: opts.minSeverity, config: opts.config,
  });
  if (opts.json) {
    console.log(JSON.stringify({ ruleCount, fileCount, findings, warnings, compileWarnRules }, null, 2));
  } else {
    for (const f of findings) {
      console.log(`${f.file}:${f.line} ${f.severity} [${f.ruleId}] ${f.message.split("\n")[0]}`);
    }
    console.error(`lean-rules: ${ruleCount} rules over ${fileCount} file(s); ${findings.length} finding(s)`);
    for (const w of warnings) console.error(`  warning: ${w.rule}: ${w.reason}`);
    for (const r of compileWarnRules) console.error(`  RULE_COMPILE_WARNING: ${r} (pattern not JS-compatible)`);
  }
  process.exit(findings.length > 0 ? 1 : 0);
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(new URL(import.meta.url).pathname)) {
  main();
}
