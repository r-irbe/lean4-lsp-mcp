// src/tree_shake.ts
// Declaration-level and module-level Lean 4 tree-shaker powered by offline
// `.ilean` reference graphs and `lean-analyzer parse --spans` UTF-8 byte spans.
// Emits standalone, kernel-verifiable, optionally anonymized Lake slices and `.tar.gz` archives.
// Scoped Unicode policy (INV-001; typographic-free by default).

import { spawn, spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { resolveLeanAnalyzerBin } from "./autoslim.ts";
import { resolveProjectRoot } from "./project_root.ts";

export interface TreeShakeModuleSummary {
  moduleName: string;
  sourceRelPath: string;
  keptDeclarations: number;
  prunedDeclarations: number;
  linesBefore: number;
  linesAfter: number;
  bytesBefore: number;
  bytesAfter: number;
  keptImports: string[];
  promotedImports: string[];
  fallbackFullModule: boolean;
}

export interface TreeShakeLeakHit {
  fileRelPath: string;
  line: number;
  pattern: string;
  snippet: string;
}

export interface TreeShakeReport {
  schemaVersion: 1;
  leanRoot: string;
  entryModules: string[];
  granularity: "declaration" | "module";
  dryRun: boolean;
  outputDir: string | null;
  archivePath: string | null;
  anonymized: boolean;
  totalCorpusModules: number;
  fileImportClosureModules: number;
  keptModulesCount: number;
  reachableDeclarationsCount: number;
  prunedDeclarationsCount: number;
  totalLinesBefore: number;
  totalLinesAfter: number;
  lineReductionPct: number;
  totalBytesBefore: number;
  totalBytesAfter: number;
  byteReductionPct: number;
  anonymityLeakHits: TreeShakeLeakHit[];
  buildVerified: boolean;
  buildExitCode: number | null;
  buildLogExcerpt: string;
  modules: TreeShakeModuleSummary[];
}

export interface TreeShakeOptions {
  projectRoot: string;
  entryModules: string[];
  outputDir?: string;
  archivePath?: string;
  granularity?: "declaration" | "module";
  anonymize?: boolean;
  packageName?: string;
  forbiddenPatterns?: string[];
  verifyBuild?: boolean;
  symlinkLakePackagesForVerify?: boolean;
  timeoutMs?: number;
  analyzerBin?: string;
  format?: "json" | "markdown";
}

interface IleanRawRefKey {
  c?: { m?: string; n?: string };
}

interface IleanRawFile {
  module?: string;
  directImports?: Array<string | [string, ...unknown[]]>;
  decls?: Record<string, number[]>;
  references?: Record<string, { definition?: unknown; usages?: unknown[][] }>;
}

interface ParsedDeclSpan {
  kind: "theorem" | "lemma" | "def" | "abbrev" | "structure" | "inductive" | "instance" | "example";
  name: string;
  bareName: string;
  startByte: number;
  endByte: number;
  hasGlobalAttr: boolean;
  rawText: string;
}

const GLOBAL_KEEP_ATTR_RE =
  /@\[[^\]]*\b(?:simp|ext|aesop|norm_cast|push_cast|coe|csimp|reducible|semireducible|default_instance|instance|elab_as_elim|lia|positivity|fun_prop|continuity|measurability|gcongr)\b[^\]]*\]/;

const SYNTAX_PROVIDER_RE =
  /^\s*(?:scoped\s+)?(?:macro|macro_rules|elab|elab_rules|syntax|notation|infix|infixl|infixr|prefix|postfix)\b/m;

/** Normalize a `(moduleName, declName)` pair without duplicating a leading module or package prefix. */
export function normalizeQualifiedDeclId(moduleName: string, declName: string): string {
  if (!moduleName) return declName;
  if (
    declName === moduleName ||
    declName.startsWith(moduleName + ".") ||
    (declName.includes(".") && moduleName.split(".")[0] === declName.split(".")[0])
  ) {
    return declName;
  }
  return `${moduleName}.${declName}`;
}

/** Normalize an entry target (`Foo.Bar` or `Foo/Bar.lean`) into a Lean module name. */
export function normalizeModuleSpec(spec: string, leanRoot: string): string {
  const trimmed = spec.trim();
  if (!trimmed) return "";
  if (trimmed.endsWith(".lean") || trimmed.includes("/") || trimmed.includes("\\")) {
    const abs = path.isAbsolute(trimmed) ? trimmed : path.resolve(leanRoot, trimmed);
    const rel = path.relative(leanRoot, abs).replace(/\\/g, "/");
    if (!rel.startsWith("..")) {
      return rel.replace(/\.lean$/, "").replace(/\//g, ".");
    }
    return trimmed.replace(/\.lean$/, "").replace(/[\\/]/g, ".");
  }
  return trimmed;
}

/** Collect all `.ilean` files under `<leanRoot>/.lake/build/lib/lean` (or `<leanRoot>/.lake/build/lib`). */
function collectProjectIleanFiles(leanRoot: string): string[] {
  const candidates = [
    path.join(leanRoot, ".lake", "build", "lib", "lean"),
    path.join(leanRoot, ".lake", "build", "lib"),
  ];
  let baseDir = "";
  for (const c of candidates) {
    if (fs.existsSync(c)) {
      baseDir = c;
      break;
    }
  }
  if (!baseDir) return [];
  const out: string[] = [];
  const walk = (dir: string) => {
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const ent of entries) {
      const full = path.join(dir, ent.name);
      if (ent.isDirectory()) {
        walk(full);
      } else if (ent.isFile() && ent.name.endsWith(".ilean")) {
        out.push(full);
      }
    }
  };
  walk(baseDir);
  return out;
}

/** Count all `.lean` source files belonging to the primary project prefixes (e.g. `MyProject/`). */
function countCorpusLeanFiles(leanRoot: string, topPrefixes: Set<string>): { files: number; lines: number; bytes: number } {
  let files = 0;
  let lines = 0;
  let bytes = 0;
  const walk = (dir: string) => {
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const ent of entries) {
      const full = path.join(dir, ent.name);
      if (ent.isDirectory()) {
        if (ent.name.startsWith(".") || ent.name === "node_modules") continue;
        walk(full);
      } else if (ent.isFile() && ent.name.endsWith(".lean")) {
        try {
          const buf = fs.readFileSync(full);
          files++;
          bytes += buf.length;
          let nl = 0;
          for (let i = 0; i < buf.length; i++) {
            if (buf[i] === 10) nl++;
          }
          lines += buf.length > 0 ? nl + 1 : 0;
        } catch {
          // ignore
        }
      }
    }
  };
  for (const pref of topPrefixes) {
    const topFile = path.join(leanRoot, `${pref}.lean`);
    if (fs.existsSync(topFile)) {
      try {
        const buf = fs.readFileSync(topFile);
        files++;
        bytes += buf.length;
        lines += buf.toString("utf-8").split("\n").length;
      } catch {
        // ignore
      }
    }
    const topDir = path.join(leanRoot, pref);
    if (fs.existsSync(topDir)) walk(topDir);
  }
  return { files, lines, bytes };
}

/**
 * Extract top-level prunable declaration byte spans (`theorem`, `lemma`, `def`, `abbrev`, `example`)
 * from `lean-analyzer parse <file.lean> --spans` output.
 * Falls back cleanly to empty array (preserving full module) if `lean-analyzer` is unavailable.
 */
export function parseTopLevelPrunableSpans(
  absPath: string,
  sourceBuf: Buffer,
  analyzerBin?: string | null
): ParsedDeclSpan[] {
  const bin = resolveLeanAnalyzerBin(analyzerBin || undefined);
  if (!bin) return [];
  const proc = spawnSync(bin, ["parse", absPath, "--spans"], {
    encoding: "utf-8",
    maxBuffer: 64 * 1024 * 1024,
    timeout: 15000,
  });
  if (proc.status !== 0 || !proc.stdout) return [];

  const sexpr = proc.stdout;
  // Match top-level `(theorem|lemma|def|abbrev|structure|inductive|example [l0, c0] - [l1, c1] @b0:b1 ...)`
  const headerRe =
    /\((theorem|lemma|def|abbrev|structure|inductive|example)\s+\[(\d+),\s*(\d+)\]\s*-\s*\[(\d+),\s*(\d+)\]\s*@(\d+):(\d+)/g;
  const spans: ParsedDeclSpan[] = [];
  let m: RegExpExecArray | null;
  while ((m = headerRe.exec(sexpr)) !== null) {
    const kind = m[1] as ParsedDeclSpan["kind"];
    const startByte = Number.parseInt(m[6], 10);
    const endByte = Number.parseInt(m[7], 10);
    if (
      !Number.isInteger(startByte) ||
      !Number.isInteger(endByte) ||
      startByte < 0 ||
      endByte <= startByte ||
      endByte > sourceBuf.length
    ) {
      continue;
    }
    // Extract `name: (identifier [...] @nb0:nb1 <ident>)` within the header window of this S-expr
    const preview = sexpr.slice(m.index + m[0].length, Math.min(sexpr.length, m.index + m[0].length + 16384));
    const nameMatch = preview.match(/name:\s*\(identifier\s+\[\d+,\s*\d+\]\s*-\s*\[\d+,\s*\d+\]\s*@\d+:\d+\s+([^\s)]+)\)/);
    const name = kind === "example" ? "(example)" : (nameMatch ? nameMatch[1].trim() : "");
    if (kind !== "example" && !name) continue;

    // Fix CST boundary in O(1)/O(lines) without backtracking regexes:
    // `lean-analyzer` attaches trailing `\n\nvariable (...) in` / `omit [...] in` (belonging to the NEXT decl)
    // onto the end of the previous span. Check the last non-blank line first in O(1).
    const isModInLine = (s: string): boolean =>
      /^(?:variable|omit|include|set_option|open)\b/.test(s) && /\bin$/.test(s);

    let adjEndByte = endByte;
    const rawSlice = sourceBuf.subarray(startByte, endByte).toString("utf-8");
    const sliceLines = rawSlice.split("\n");
    let k = sliceLines.length - 1;
    while (k > 0 && sliceLines[k].trim() === "") k--;
    if (k > 0 && isModInLine(sliceLines[k].trim())) {
      let cutIdx = k;
      let j = k - 1;
      while (j > 0) {
        const tr = sliceLines[j].trim();
        if (tr === "") {
          j--;
          continue;
        }
        if (isModInLine(tr) || tr.startsWith("--") || (tr.startsWith("/-") && tr.endsWith("-/"))) {
          cutIdx = j;
          j--;
          continue;
        }
        break;
      }
      const keptPrefix = sliceLines.slice(0, cutIdx).join("\n");
      const nextEnd = startByte + Buffer.byteLength(keptPrefix, "utf-8");
      if (nextEnd > startByte) {
        adjEndByte = nextEnd;
      }
    }

    const rawText = sourceBuf.subarray(startByte, adjEndByte).toString("utf-8");
    const bareName = name.includes(".") ? name.split(".").pop()! : name;
    const codeNoComments = stripLeanCommentsAndStrings(rawText).trimStart();
    const hasGlobalAttr =
      kind !== "structure" &&
      kind !== "inductive" &&
      GLOBAL_KEEP_ATTR_RE.test(codeNoComments.slice(0, 600));
    spans.push({
      kind,
      name,
      bareName,
      startByte,
      endByte: adjEndByte,
      hasGlobalAttr,
      rawText,
    });
  }
  spans.sort((a, b) => a.startByte - b.startByte || b.endByte - a.endByte);
  // Deduplicate/drop overlapping spans and attach each declaration's own preceding `variable/omit/include/set_option/open ... in` lines
  const isModLine = (s: string): boolean =>
    /^(?:variable|omit|include|set_option|open)\b/.test(s) && /\bin$/.test(s);
  const clean: ParsedDeclSpan[] = [];
  let lastEnd = 0;
  for (const sp of spans) {
    if (sp.startByte < lastEnd) continue;
    let adjStart = sp.startByte;
    if (adjStart > lastEnd) {
      const gapText = sourceBuf.subarray(lastEnd, adjStart).toString("utf-8");
      const gapLines = gapText.split("\n");
      let idx = gapLines.length - 1;
      while (idx >= 0 && gapLines[idx].trim() === "") idx--;
      if (idx >= 0 && isModLine(gapLines[idx].trim())) {
        let modStart = idx;
        let p = idx - 1;
        while (p >= 0) {
          const tr = gapLines[p].trim();
          if (tr === "") {
            p--;
            continue;
          }
          if (isModLine(tr)) {
            modStart = p;
            p--;
            continue;
          }
          break;
        }
        const suffix = gapLines.slice(modStart).join("\n");
        const prefixBytes = Buffer.byteLength(suffix, "utf-8");
        if (adjStart - prefixBytes >= lastEnd) {
          adjStart -= prefixBytes;
        }
      }
    }
    const finalRaw =
      adjStart !== sp.startByte
        ? sourceBuf.subarray(adjStart, sp.endByte).toString("utf-8")
        : sp.rawText;
    const finalNoComments = stripLeanCommentsAndStrings(finalRaw).trimStart();
    clean.push({
      ...sp,
      startByte: adjStart,
      hasGlobalAttr:
        sp.kind !== "structure" &&
        sp.kind !== "inductive" &&
        GLOBAL_KEEP_ATTR_RE.test(finalNoComments.slice(0, 600)),
      rawText: finalRaw,
    });
    lastEnd = sp.endByte;
  }
  return clean;
}

/**
 * Stack-overflow-immune fallback span extractor using `.ilean` compiler declaration coordinates
 * (`decls: { name: [startLine0, startCol0, endLine0, endCol0, ...] }`) when `lean-analyzer`
 * overflows its stack on multi-thousand-line modules.
 */
export function parseIleanFallbackSpans(
  sourceText: string,
  sourceBuf: Buffer,
  ileanDecls?: Record<string, number[]>
): ParsedDeclSpan[] {
  if (!ileanDecls) return [];
  const srcLines = sourceText.split("\n");
  const lineStartByte: number[] = new Array(srcLines.length);
  let acc = 0;
  for (let i = 0; i < srcLines.length; i++) {
    lineStartByte[i] = acc;
    acc += Buffer.byteLength(srcLines[i], "utf-8") + 1;
  }
  const toByte = (line0: number, colUtf16: number): number => {
    if (line0 < 0) return 0;
    if (line0 >= srcLines.length) return sourceBuf.length;
    const ln = srcLines[line0];
    const clampedCol = Math.max(0, Math.min(ln.length, colUtf16));
    return lineStartByte[line0] + Buffer.byteLength(ln.slice(0, clampedCol), "utf-8");
  };

  const rawSpans: ParsedDeclSpan[] = [];
  for (const [rawDeclName, coords] of Object.entries(ileanDecls)) {
    if (!Array.isArray(coords) || coords.length < 4) continue;
    const [sL, sC, eL, eC] = coords;
    if (sC < 0 || sL < 0 || eL < sL || eL >= srcLines.length) continue;
    const startByte = toByte(sL, sC);
    const endByte = toByte(eL, eC);
    if (endByte <= startByte || endByte > sourceBuf.length) continue;

    const rawText = sourceBuf.subarray(startByte, endByte).toString("utf-8");
    const codeHead = stripLeanCommentsAndStrings(rawText).trimStart().slice(0, 1200);
    const kwMatch = codeHead.match(
      /^\s*(?:@\[[^\]]*\]\s*|(?:\b(?:private|protected|noncomputable|partial|unsafe|scoped|local)\b)\s*)*(theorem|lemma|def|abbrev|structure|inductive|instance)\b/
    );
    if (!kwMatch) continue;
    const kind = kwMatch[1] as ParsedDeclSpan["kind"];
    const cleanName = rawDeclName.startsWith("_private.")
      ? rawDeclName.split(".").pop() || rawDeclName
      : rawDeclName;
    const bareName = cleanName.includes(".") ? cleanName.split(".").pop()! : cleanName;
    const hasGlobalAttr =
      kind === "instance" ||
      (kind !== "structure" &&
        kind !== "inductive" &&
        GLOBAL_KEEP_ATTR_RE.test(codeHead.slice(0, 600)));
    rawSpans.push({
      kind,
      name: cleanName,
      bareName,
      startByte,
      endByte,
      hasGlobalAttr,
      rawText,
    });
  }

  // Also capture anonymous column-0 `example ...` blocks (which are omitted from `.ilean` `decls`)
  for (let i = 0; i < srcLines.length; i++) {
    if (/^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?example\b/.test(srcLines[i])) {
      let exStartLine = i;
      // Include attached `/-- ... -/` doc comment immediately above `example`
      if (i > 0 && srcLines[i - 1].trimEnd().endsWith("-/")) {
        let d = i - 1;
        while (d >= 0) {
          if (srcLines[d].trimStart().startsWith("/--")) {
            exStartLine = d;
            break;
          }
          if (srcLines[d].trimStart().startsWith("/-")) break;
          d--;
        }
      }
      let exEndLine = i;
      while (exEndLine + 1 < srcLines.length) {
        const nxt = srcLines[exEndLine + 1];
        if (nxt === "" || /^[ \t]+/.test(nxt)) {
          exEndLine++;
          continue;
        }
        break;
      }
      while (exEndLine > i && srcLines[exEndLine].trim() === "") {
        exEndLine--;
      }
      const startByte = lineStartByte[exStartLine];
      const endByte = toByte(exEndLine, srcLines[exEndLine].length);
      if (endByte > startByte) {
        rawSpans.push({
          kind: "example",
          name: "(example)",
          bareName: "(example)",
          startByte,
          endByte,
          hasGlobalAttr: false,
          rawText: sourceBuf.subarray(startByte, endByte).toString("utf-8"),
        });
      }
      i = exEndLine;
    }
  }

  rawSpans.sort((a, b) => a.startByte - b.startByte || b.endByte - a.endByte);
  const isModLine = (s: string): boolean =>
    /^(?:variable|omit|include|set_option|open)\b/.test(s) && /\bin$/.test(s);
  const clean: ParsedDeclSpan[] = [];
  let lastEnd = 0;
  for (const sp of rawSpans) {
    if (sp.startByte < lastEnd) continue;
    let adjStart = sp.startByte;
    if (adjStart > lastEnd) {
      const gapText = sourceBuf.subarray(lastEnd, adjStart).toString("utf-8");
      const gapLines = gapText.split("\n");
      let idx = gapLines.length - 1;
      while (idx >= 0 && gapLines[idx].trim() === "") idx--;
      if (idx >= 0 && isModLine(gapLines[idx].trim())) {
        let modStart = idx;
        let p = idx - 1;
        while (p >= 0) {
          const tr = gapLines[p].trim();
          if (tr === "") {
            p--;
            continue;
          }
          if (isModLine(tr)) {
            modStart = p;
            p--;
            continue;
          }
          break;
        }
        const suffix = gapLines.slice(modStart).join("\n");
        const prefixBytes = Buffer.byteLength(suffix, "utf-8");
        if (adjStart - prefixBytes >= lastEnd) {
          adjStart -= prefixBytes;
        }
      }
    }
    const finalRaw =
      adjStart !== sp.startByte
        ? sourceBuf.subarray(adjStart, sp.endByte).toString("utf-8")
        : sp.rawText;
    clean.push({
      ...sp,
      startByte: adjStart,
      rawText: finalRaw,
    });
    lastEnd = sp.endByte;
  }
  return clean;
}

/** Strip identifying lines in leading copyright/author block comments and URLs when `anonymize` is enabled. */
export function anonymizeLeanSource(sourceText: string): string {
  let out = sourceText;
  // Replace leading `/- ... -/` header if it mentions Copyright / Authors
  out = out.replace(/^\/-[\s\S]*?-\/\s*\n?/, (hdr) => {
    if (/Copyright|Authors?:/i.test(hdr)) {
      return [
        "/-",
        "Released under Apache 2.0 license.",
        "Anonymized supplementary artifact for double-blind peer review.",
        "-/",
        "",
      ].join("\n");
    }
    return hdr;
  });
  // Scrub any github.com/<owner>/<repo> user URLs in comments (preserving leanprover / leanprover-community / argumentcomputer)
  out = out.replace(
    /https?:\/\/github\.com\/(?!(?:leanprover|leanprover-community|argumentcomputer|ammkrn)\b)[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+/g,
    "https://anonymous.4open.science/r/anonymized-artifact"
  );
  return out;
}

/** Strip nested `/- ... -/` comments, `-- ...` line comments, and `"..."` strings while preserving newlines. */
export function stripLeanCommentsAndStrings(src: string): string {
  const out: string[] = [];
  let i = 0;
  const n = src.length;
  let blockDepth = 0;
  while (i < n) {
    const ch = src[i];
    const nxt = i + 1 < n ? src[i + 1] : "";
    if (blockDepth > 0) {
      if (ch === "/" && nxt === "-") {
        blockDepth++;
        out.push("  ");
        i += 2;
      } else if (ch === "-" && nxt === "/") {
        blockDepth--;
        out.push("  ");
        i += 2;
      } else {
        out.push(ch === "\n" ? "\n" : " ");
        i++;
      }
      continue;
    }
    if (ch === "/" && nxt === "-") {
      blockDepth = 1;
      out.push("  ");
      i += 2;
      continue;
    }
    if (ch === "-" && nxt === "-") {
      while (i < n && src[i] !== "\n") {
        out.push(" ");
        i++;
      }
      continue;
    }
    if (ch === '"') {
      out.push(" ");
      i++;
      while (i < n && src[i] !== '"') {
        if (src[i] === "\\" && i + 1 < n) {
          out.push("  ");
          i += 2;
        } else {
          out.push(src[i] === "\n" ? "\n" : " ");
          i++;
        }
      }
      if (i < n) {
        out.push(" ");
        i++;
      }
      continue;
    }
    out.push(ch);
    i++;
  }
  return out.join("");
}

/** Rewrite top-of-file `import ...` lines (and prune `open <DroppedMod>` lines) to keep external + kept/promoted imports. */
export function rewriteModuleImports(
  sourceText: string,
  isProjectModule: (mod: string) => boolean,
  keptProjectImports: ReadonlySet<string>,
  promotedProjectImports: readonly string[],
  allKeptModules?: ReadonlySet<string>,
  isNamespaceUnavailable?: (ns: string) => boolean,
  isIdentUnavailableInVariable?: (ident: string) => boolean
): string {
  const lines = sourceText.split("\n");
  const outLines: string[] = [];
  const emittedImports = new Set<string>();
  let lastKeptImportIdx = -1;

  const isDroppedProjNamespace = (ns: string): boolean => {
    const cleanNs = ns.replace(/\($/, "").trim();
    if (!cleanNs) return false;
    if (isNamespaceUnavailable && isNamespaceUnavailable(cleanNs)) {
      return true;
    }
    const parts = cleanNs.split(".");
    // Never check `len === 1` (root package umbrella like `MyPkg`), because `open MyPkg.SomeSubns`
    // may open a namespace declared inside a kept module (`MyPkg.Dynamics.StageMatrix`) even when `MyPkg.lean` umbrella is unkept.
    for (let len = parts.length; len >= 2; len--) {
      const pref = parts.slice(0, len).join(".");
      if (isProjectModule(pref)) {
        const keptSet = allKeptModules ?? keptProjectImports;
        return !keptSet.has(pref);
      }
    }
    return false;
  };

  // Collect variable names bound locally by `variable (... : ...)` / `{... : ...}` in this file
  // so type-variable names (`State`, `E`, `B`, `I`, `T`) are never mistaken for unavailable external constants.
  const localBoundVars = new Set<string>();
  for (const ln of lines) {
    if (/^\s*variable\b/.test(ln)) {
      const binderMatches = ln.matchAll(/[\({\[]([^()\[\]{}:]+):/g);
      for (const bm of binderMatches) {
        for (const tok of bm[1].trim().split(/\s+/)) {
          if (tok) localBoundVars.add(tok);
        }
      }
    }
  }

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const m = line.match(/^\s*import\s+([A-Za-z0-9_.']+)\s*(?:--.*)?$/);
    if (m) {
      const impMod = m[1];
      if (isProjectModule(impMod) && !keptProjectImports.has(impMod)) {
        continue;
      }
      if (emittedImports.has(impMod)) continue;
      emittedImports.add(impMod);
      lastKeptImportIdx = outLines.length;
      outLines.push(`import ${impMod}`);
      continue;
    }
    const openMatch = line.match(/^\s*(?:scoped\s+)?open\s+([A-Za-z0-9_.']+(?:\s+[A-Za-z0-9_.']+)*)\s*(?:\([^)]*\))?\s*(?:--.*)?$/);
    if (openMatch) {
      const targets = openMatch[1].trim().split(/\s+/);
      const keptTargets = targets.filter((t) => !isDroppedProjNamespace(t));
      if (keptTargets.length === 0) {
        continue;
      }
      if (keptTargets.length < targets.length) {
        outLines.push(line.replace(openMatch[1], keptTargets.join(" ")));
        continue;
      }
    }
    // Only prune standalone `variable [...]` instance-assumption lines (no `:` binders) that reference
    // an unimported multi-char project type (e.g. `variable [Fintype MDPState]` when `MDPState`'s module was pruned).
    if (
      isIdentUnavailableInVariable &&
      /^\s*variable\s+\[/.test(line) &&
      !line.includes(":") &&
      !/\bin\s*(?:--.*)?$/.test(line)
    ) {
      const idents = line.match(/\b[A-Z][A-Za-z0-9_']{2,}\b/g) || [];
      if (idents.some((id) => !localBoundVars.has(id) && isIdentUnavailableInVariable(id))) {
        continue;
      }
    }
    outLines.push(line);
  }

  const extraToInsert = promotedProjectImports.filter((imp) => !emittedImports.has(imp));
  if (extraToInsert.length > 0) {
    const insertLines = extraToInsert.map((imp) => `import ${imp}`);
    if (lastKeptImportIdx >= 0) {
      outLines.splice(lastKeptImportIdx + 1, 0, ...insertLines);
    } else {
      // Insert after leading `/- ... -/` header comment (not `/-! ... -/` module docstring!) if present
      let insertAt = 0;
      if (outLines[0]?.trimStart().startsWith("/-") && !outLines[0]?.trimStart().startsWith("/-!")) {
        for (let k = 0; k < outLines.length; k++) {
          if (outLines[k].includes("-/")) {
            insertAt = k + 1;
            break;
          }
        }
      }
      outLines.splice(insertAt, 0, ...insertLines);
    }
  }
  return outLines.join("\n");
}

/**
 * Prune unreachable top-level declarations in a non-entry Lean file using UTF-8 byte spans
 * and an in-file lexical fixed-point closure so local helper/macro/attribute references stay intact.
 */
export function pruneModuleDeclarations(
  absPath: string,
  sourceText: string,
  reachableBareNames: ReadonlySet<string>,
  reachableQualSuffixes: ReadonlySet<string>,
  analyzerBin?: string | null,
  ileanDecls?: Record<string, number[]>,
  canKeepGlobalAttr?: (sp: ParsedDeclSpan) => boolean
): { prunedText: string; keptCount: number; prunedCount: number } {
  const buf = Buffer.from(sourceText, "utf-8");
  const hasFullCompilerSpans = Boolean(
    ileanDecls && Object.values(ileanDecls).some((c) => Array.isArray(c) && c.length >= 8)
  );
  let spans = hasFullCompilerSpans
    ? parseIleanFallbackSpans(sourceText, buf, ileanDecls)
    : parseTopLevelPrunableSpans(absPath, buf, analyzerBin);
  if (spans.length === 0) {
    spans = hasFullCompilerSpans
      ? parseTopLevelPrunableSpans(absPath, buf, analyzerBin)
      : parseIleanFallbackSpans(sourceText, buf, ileanDecls);
  }
  if (spans.length === 0) {
    return { prunedText: sourceText, keptCount: 0, prunedCount: 0 };
  }

  const isInitiallyKept = (sp: ParsedDeclSpan): boolean => {
    if (sp.kind === "example") return false;
    if (sp.hasGlobalAttr && (!canKeepGlobalAttr || canKeepGlobalAttr(sp))) return true;
    // Keep `def` and `abbrev` if referenced OR if they define coercions/projections/types;
    // prune `def`/`abbrev`/`theorem`/`lemma` when unreferenced.
    if (reachableBareNames.has(sp.bareName) || reachableBareNames.has(sp.name)) {
      return true;
    }
    for (const suf of reachableQualSuffixes) {
      if (suf === sp.name || suf.endsWith("." + sp.name) || suf.endsWith("." + sp.bareName)) {
        return true;
      }
    }
    return false;
  };

  const keptFlags = spans.map(isInitiallyKept);

  // Build baseline skeleton text (everything outside prunable spans + already-kept spans)
  const buildKeptCorpus = (): string => {
    const chunks: Buffer[] = [];
    let cursor = 0;
    for (let i = 0; i < spans.length; i++) {
      const sp = spans[i];
      if (sp.startByte > cursor) {
        chunks.push(buf.subarray(cursor, sp.startByte));
      }
      if (keptFlags[i]) {
        chunks.push(buf.subarray(sp.startByte, sp.endByte));
      }
      cursor = sp.endByte;
    }
    if (cursor < buf.length) {
      chunks.push(buf.subarray(cursor));
    }
    return Buffer.concat(chunks).toString("utf-8");
  };

  // Extract all identifier-like words in a string in O(|text|) so fixed-point takes < 2 ms per file
  const extractIdentifierSet = (txt: string): Set<string> => {
    const set = new Set<string>();
    const idRe = /[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2080-\u2089]*/g;
    let m: RegExpExecArray | null;
    while ((m = idRe.exec(txt)) !== null) {
      set.add(m[0]);
    }
    return set;
  };

  // Strip top-level `#check` / `#eval` / `#print` smoke lines from skeleton before fixed-point
  // so smoke checks in library modules do not artificially keep dead theorems (nor break after pruning).
  const stripSmokeCommands = (txt: string): string =>
    txt
      .split("\n")
      .filter((ln) => !/^\s*#(?:check|eval|print|reduce)\b/.test(ln))
      .join("\n");

  // Strip `import`/`namespace`/`section`/`end` header lines so e.g. `namespace Foo.RefinementTower`
  // never causes `activeTokens` to falsely revive an unreferenced `structure RefinementTower`.
  const stripStructuralHeaderLines = (txt: string): string =>
    txt
      .split("\n")
      .filter((ln) => !/^\s*(?:import|namespace|section|end)\b/.test(ln))
      .join("\n");

  let changed = true;
  while (changed) {
    changed = false;
    const codeOnly = stripStructuralHeaderLines(
      stripLeanCommentsAndStrings(stripSmokeCommands(buildKeptCorpus()))
    );
    const activeTokens = extractIdentifierSet(codeOnly);
    for (let i = 0; i < spans.length; i++) {
      if (keptFlags[i]) continue;
      const sp = spans[i];
      if (sp.kind === "example") continue;
      if (sp.bareName && activeTokens.has(sp.bareName)) {
        keptFlags[i] = true;
        changed = true;
      }
    }
  }

  let keptCount = 0;
  let prunedCount = 0;
  const outChunks: Buffer[] = [];
  let cursor = 0;
  for (let i = 0; i < spans.length; i++) {
    const sp = spans[i];
    if (sp.startByte > cursor) {
      outChunks.push(buf.subarray(cursor, sp.startByte));
    }
    if (keptFlags[i]) {
      keptCount++;
      outChunks.push(buf.subarray(sp.startByte, sp.endByte));
    } else {
      prunedCount++;
    }
    cursor = sp.endByte;
  }
  if (cursor < buf.length) {
    outChunks.push(buf.subarray(cursor));
  }

  let prunedText = stripSmokeCommands(Buffer.concat(outChunks).toString("utf-8"));
  // Collapse 3+ consecutive blank lines left behind by pruned spans into 2 newlines
  prunedText = prunedText.replace(/\n{3,}/g, "\n\n");
  return { prunedText, keptCount, prunedCount };
}

/** Run `lake build <targets>` asynchronously with bounded timeout. */
function runLakeBuildAsync(
  cwd: string,
  targets: readonly string[],
  timeoutMs: number
): Promise<{ exitCode: number; output: string }> {
  return new Promise((resolve) => {
    const elanBin = path.join(os.homedir(), ".elan", "bin");
    const basePath = process.env.PATH || "";
    const envPath =
      fs.existsSync(elanBin) && !basePath.split(path.delimiter).includes(elanBin)
        ? `${elanBin}${path.delimiter}${basePath}`
        : basePath;
    const childEnv: NodeJS.ProcessEnv = { ...process.env, PATH: envPath };
    const lakeArgs: string[] = [];
    const tcFile = path.join(cwd, "lean-toolchain");
    if (fs.existsSync(tcFile)) {
      const tcRaw = fs.readFileSync(tcFile, "utf-8").trim();
      if (tcRaw) {
        const shortVer = tcRaw.replace(/^leanprover\/lean4:/, "");
        if (/^v4\.\d+\.\d+/.test(shortVer)) {
          lakeArgs.push(`+${shortVer}`);
        }
      }
    }
    lakeArgs.push("build", ...targets);
    const child = spawn("lake", lakeArgs, {
      cwd,
      stdio: ["ignore", "pipe", "pipe"],
      env: childEnv,
    });
    let output = "";
    let settled = false;
    const append = (chunk: Buffer | string) => {
      output += chunk.toString();
      if (output.length > 512 * 1024) {
        output = output.slice(-512 * 1024);
      }
    };
    child.stdout?.on("data", append);
    child.stderr?.on("data", append);
    const timer = setTimeout(() => {
      if (settled) return;
      settled = true;
      try {
        child.kill("SIGTERM");
      } catch {
        // ignore
      }
      resolve({ exitCode: 124, output: `${output}\n[timeout after ${timeoutMs}ms]` });
    }, timeoutMs);
    child.on("error", (err) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve({ exitCode: 1, output: `${output}\n${err.message}` });
    });
    child.on("close", (code) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve({ exitCode: code ?? 1, output });
    });
  });
}

/** Generate a minimal, clean Lake configuration matching `lean-manifest.json` dependencies. */
function buildStandaloneLakefile(
  leanRoot: string,
  packageName: string,
  topPrefixes: readonly string[],
  anonymize: boolean
): { filename: string; content: string } {
  const origLakefileLean = path.join(leanRoot, "lakefile.lean");
  const origLakefileToml = path.join(leanRoot, "lakefile.toml");

  if (!anonymize && fs.existsSync(origLakefileToml)) {
    return { filename: "lakefile.toml", content: fs.readFileSync(origLakefileToml, "utf-8") };
  }

  // Extract `require ...` blocks from `lakefile.lean` if present so package pins match `lake-manifest.json`
  let requireBlocks: string[] = [];
  if (fs.existsSync(origLakefileLean)) {
    const raw = fs.readFileSync(origLakefileLean, "utf-8");
    const reqRe = /^\s*require\s+[A-Za-z0-9_]+\s+from\s+git\s*\n?\s*"[^"]+"\s*@\s*"[^"]+"/gm;
    let m: RegExpExecArray | null;
    while ((m = reqRe.exec(raw)) !== null) {
      requireBlocks.push(m[0].trim());
    }
  }
  if (requireBlocks.length === 0) {
    const manifestPath = path.join(leanRoot, "lake-manifest.json");
    if (fs.existsSync(manifestPath)) {
      try {
        const mf = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
        for (const pkg of mf.packages || []) {
          if (pkg && pkg.inherited === false && pkg.name && pkg.url && (pkg.inputRev || pkg.rev)) {
            requireBlocks.push(`require ${pkg.name} from git\n  "${pkg.url}" @ "${pkg.inputRev || pkg.rev}"`);
          }
        }
      } catch {
        // ignore
      }
    }
  }

  const roots = topPrefixes.length > 0 ? topPrefixes : [packageName];
  const libBlocks = roots.map(
    (pref) =>
      `@[default_target]\nlean_lib ${pref} where\n  srcDir := "."\n  globs := #[.submodules \`${pref}]`
  );

  const content = [
    "import Lake",
    "open Lake DSL",
    "",
    `package ${packageName} where`,
    "  leanOptions := #[",
    "    \u27e8`autoImplicit, false\u27e9,",
    "    \u27e8`weak.linter.unusedTactic, false\u27e9",
    "  ]",
    "",
    ...requireBlocks.flatMap((r) => [r, ""]),
    ...libBlocks,
    "",
  ].join("\n");

  return { filename: "lakefile.lean", content };
}

/** Scan all text files under `dir` (skipping `.lake`) for forbidden identity patterns. */
export function scanDirectoryForIdentityLeaks(
  dir: string,
  forbiddenPatterns: readonly string[]
): TreeShakeLeakHit[] {
  const patterns = forbiddenPatterns.map((p) => p.trim()).filter(Boolean);
  if (patterns.length === 0) return [];
  const lowerPatterns = patterns.map((p) => p.toLowerCase());
  const hits: TreeShakeLeakHit[] = [];

  const walk = (curr: string) => {
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(curr, { withFileTypes: true });
    } catch {
      return;
    }
    for (const ent of entries) {
      if (ent.name === ".lake" || ent.name === ".git" || ent.name === "node_modules") continue;
      const full = path.join(curr, ent.name);
      if (ent.isDirectory()) {
        walk(full);
      } else if (ent.isFile()) {
        let text = "";
        try {
          text = fs.readFileSync(full, "utf-8");
        } catch {
          continue;
        }
        const lines = text.split("\n");
        const rel = path.relative(dir, full).replace(/\\/g, "/");
        for (let i = 0; i < lines.length; i++) {
          const rawLine = lines[i];
          const low = rawLine.toLowerCase();
          for (let pIdx = 0; pIdx < lowerPatterns.length; pIdx++) {
            const lp = lowerPatterns[pIdx];
            let pos = low.indexOf(lp);
            while (pos !== -1) {
              const prev = pos > 0 ? rawLine[pos - 1] : "";
              const next = pos + lp.length < rawLine.length ? rawLine[pos + lp.length] : "";
              const prevIsAlnum = /[A-Za-z0-9]/.test(prev);
              const nextIsLowerOrDigit = /[a-z0-9]/.test(next);
              if (!prevIsAlnum && !nextIsLowerOrDigit) {
                hits.push({
                  fileRelPath: rel,
                  line: i + 1,
                  pattern: patterns[pIdx],
                  snippet: rawLine.trim().slice(0, 140),
                });
                break;
              }
              pos = low.indexOf(lp, pos + 1);
            }
          }
        }
      }
    }
  };
  walk(dir);
  return hits;
}

/** Format a `TreeShakeReport` as concise Markdown. */
export function formatTreeShakeMarkdown(rep: TreeShakeReport): string {
  const lines = [
    `# Lean 4 Tree-Shake Report`,
    ``,
    `- **Lean Root**: \`${rep.leanRoot}\``,
    `- **Entry Modules**: ${rep.entryModules.map((m) => `\`${m}\``).join(", ")}`,
    `- **Granularity**: \`${rep.granularity}\` (${rep.dryRun ? "dry-run" : "emitted"})`,
    `- **Modules**: \`${rep.keptModulesCount}\` kept (from \`${rep.fileImportClosureModules}\` imported / \`${rep.totalCorpusModules}\` total corpus modules)`,
    `- **Declarations**: \`${rep.reachableDeclarationsCount}\` reachable, \`${rep.prunedDeclarationsCount}\` pruned in kept modules`,
    `- **LOC Reduction**: \`${rep.totalLinesBefore}\` -> \`${rep.totalLinesAfter}\` (\`-${rep.lineReductionPct.toFixed(1)}%\`)`,
    `- **Byte Reduction**: \`${rep.totalBytesBefore}\` -> \`${rep.totalBytesAfter}\` (\`-${rep.byteReductionPct.toFixed(1)}%\`)`,
    `- **Anonymity Leaks**: \`${rep.anonymityLeakHits.length}\``,
    `- **Kernel Build Verified**: \`${rep.buildVerified}\`${rep.buildExitCode !== null ? ` (exit=${rep.buildExitCode})` : ""}`,
  ];
  if (rep.outputDir) lines.push(`- **Output Directory**: \`${rep.outputDir}\``);
  if (rep.archivePath) lines.push(`- **Archive Path**: \`${rep.archivePath}\``);
  if (!rep.buildVerified && rep.buildExitCode !== null && rep.buildLogExcerpt) {
    lines.push("", "## Build Log Excerpt", "```text", rep.buildLogExcerpt, "```");
  }
  return lines.join("\n");
}

/**
 * Main entry point: computes `.ilean` transitive declaration/module closure, optionally
 * prunes unreachable declarations via `lean-analyzer parse --spans`, emits an optional
 * standalone anonymized Lake slice + deterministic `.tar.gz`, and verifies `lake build`.
 */
export async function runLeanTreeShake(options: TreeShakeOptions): Promise<TreeShakeReport> {
  const leanRoot = resolveProjectRoot(options.projectRoot, {}).root;
  const granularity = options.granularity ?? "declaration";
  const anonymize = options.anonymize === true;
  const entryModules = options.entryModules
    .map((m) => normalizeModuleSpec(m, leanRoot))
    .filter(Boolean);
  if (entryModules.length === 0) {
    throw new Error("runLeanTreeShake requires at least one entryModule");
  }

  const ileanPaths = collectProjectIleanFiles(leanRoot);
  if (ileanPaths.length === 0) {
    throw new Error(
      `No compiled .ilean files found under ${leanRoot}/.lake/build/lib; run 'lake build ${entryModules.join(" ")}' first`
    );
  }

  const moduleSourceRel = new Map<string, string>();
  const moduleDirectImports = new Map<string, string[]>();
  const moduleDecls = new Map<string, Set<string>>();
  // callerQualId -> Array<{ targetModule, targetId, rawName }>
  const declEdges = new Map<string, Array<{ targetModule: string; targetId: string; rawName: string }>>();
  // module -> set of referenced target modules (across all usages in the file, or per decl)
  const moduleTopRefs = new Map<string, Array<{ targetModule: string; targetId: string; rawName: string }>>();
  const declRefModules = new Map<string, Set<string>>();

  // Pass 1: load all project `.ilean` files whose `.lean` source exists under `leanRoot`
  const parsedIleans = new Map<string, IleanRawFile>();
  const topPrefixes = new Set<string>();
  const namespaceToModules = new Map<string, Set<string>>();
  const shortDeclToModules = new Map<string, Set<string>>();

  for (const ip of ileanPaths) {
    let parsed: IleanRawFile;
    try {
      parsed = JSON.parse(fs.readFileSync(ip, "utf-8")) as IleanRawFile;
    } catch {
      continue;
    }
    const mod = String(parsed.module || "").trim();
    if (!mod) continue;
    const relLean = mod.replace(/\./g, "/") + ".lean";
    const absLean = path.join(leanRoot, relLean);
    if (!fs.existsSync(absLean)) continue;

    moduleSourceRel.set(mod, relLean);
    parsedIleans.set(mod, parsed);
    topPrefixes.add(mod.split(".")[0]);

    const declSet = new Set<string>();
    if (parsed.decls && typeof parsed.decls === "object") {
      for (const dName of Object.keys(parsed.decls)) {
        declSet.add(dName);
        declSet.add(normalizeQualifiedDeclId(mod, dName));
        if (!dName.startsWith("_private.")) {
          const parts = dName.split(".");
          const shortName = parts[parts.length - 1];
          if (shortName) {
            let sMods = shortDeclToModules.get(shortName);
            if (!sMods) {
              sMods = new Set<string>();
              shortDeclToModules.set(shortName, sMods);
            }
            sMods.add(mod);
          }
          for (let len = 2; len < parts.length; len++) {
            const nsPref = parts.slice(0, len).join(".");
            let nsMods = namespaceToModules.get(nsPref);
            if (!nsMods) {
              nsMods = new Set<string>();
              namespaceToModules.set(nsPref, nsMods);
            }
            nsMods.add(mod);
          }
        }
      }
    }
    moduleDecls.set(mod, declSet);

    const imps: string[] = [];
    if (Array.isArray(parsed.directImports)) {
      for (const item of parsed.directImports) {
        if (Array.isArray(item) && typeof item[0] === "string") {
          imps.push(item[0]);
        } else if (typeof item === "string") {
          imps.push(item);
        }
      }
    }
    moduleDirectImports.set(mod, imps);
  }

  for (const em of entryModules) {
    if (!moduleSourceRel.has(em)) {
      throw new Error(
        `Entry module '${em}' not found in compiled .ilean index under ${leanRoot}; run 'lake build ${em}' first`
      );
    }
  }

  const isProjectModule = (m: string): boolean => moduleSourceRel.has(m);

  // Pass 2: compute file-level `directImports` closure from `entryModules`
  const fileClosure = new Set<string>();
  const modQueue: string[] = [...entryModules];
  while (modQueue.length > 0) {
    const curr = modQueue.shift()!;
    if (fileClosure.has(curr) || !isProjectModule(curr)) continue;
    fileClosure.add(curr);
    for (const imp of moduleDirectImports.get(curr) || []) {
      if (isProjectModule(imp) && !fileClosure.has(imp)) {
        modQueue.push(imp);
      }
    }
  }

  // Detect syntax/macro/notation provider modules inside `fileClosure`
  const syntaxModules = new Set<string>();
  for (const mod of fileClosure) {
    const absLean = path.join(leanRoot, moduleSourceRel.get(mod)!);
    try {
      const txt = fs.readFileSync(absLean, "utf-8");
      if (SYNTAX_PROVIDER_RE.test(txt)) {
        syntaxModules.add(mod);
      }
    } catch {
      // ignore
    }
  }

  // Pass 3: extract declaration-to-declaration edges within `fileClosure`
  for (const mod of fileClosure) {
    const parsed = parsedIleans.get(mod);
    if (!parsed?.references || typeof parsed.references !== "object") continue;
    for (const [encKey, refObj] of Object.entries(parsed.references)) {
      let cObj: IleanRawRefKey | null = null;
      try {
        cObj = JSON.parse(encKey) as IleanRawRefKey;
      } catch {
        continue;
      }
      const refMod = cObj?.c?.m;
      const refName = cObj?.c?.n;
      if (!refMod || !refName || !fileClosure.has(refMod)) continue;

      const targetId = normalizeQualifiedDeclId(refMod, refName);
      const usages = Array.isArray(refObj?.usages) ? refObj.usages : [];
      if (usages.length === 0) continue;

      for (const u of usages) {
        const callerRaw = typeof u?.[4] === "string" ? u[4] : "";
        if (!callerRaw || callerRaw === "_check" || entryModules.includes(mod)) {
          let topList = moduleTopRefs.get(mod);
          if (!topList) {
            topList = [];
            moduleTopRefs.set(mod, topList);
          }
          topList.push({ targetModule: refMod, targetId, rawName: refName });
        }
        if (callerRaw && callerRaw !== "_check") {
          const callerId = normalizeQualifiedDeclId(mod, callerRaw);
          let list = declEdges.get(callerId);
          if (!list) {
            list = [];
            declEdges.set(callerId, list);
          }
          list.push({ targetModule: refMod, targetId, rawName: refName });

          let usedMods = declRefModules.get(callerId);
          if (!usedMods) {
            usedMods = new Set<string>();
            declRefModules.set(callerId, usedMods);
          }
          usedMods.add(refMod);
        }
      }
    }
  }

  // Pass 4: BFS over `(module, declId)` starting from `entryModules`
  const keptModules = new Set<string>();
  const reachableByModule = new Map<string, Set<string>>();
  const usedModulesByModule = new Map<string, Set<string>>();
  const visitedDeclKeys = new Set<string>();
  const declQueue: Array<{ mod: string; declId: string; rawName: string }> = [];

  const markModuleKept = (mod: string) => {
    if (!fileClosure.has(mod)) return;
    const isNew = !keptModules.has(mod);
    keptModules.add(mod);
    if (!reachableByModule.has(mod)) reachableByModule.set(mod, new Set<string>());
    if (!usedModulesByModule.has(mod)) usedModulesByModule.set(mod, new Set<string>());
    if (isNew) {
      // Keep any syntax-providing module directly imported by `mod`
      for (const imp of moduleDirectImports.get(mod) || []) {
        if (syntaxModules.has(imp)) {
          usedModulesByModule.get(mod)!.add(imp);
          markSyntaxModuleClosure(imp);
        }
      }
    }
  };

  const markSyntaxModuleClosure = (synMod: string) => {
    if (keptModules.has(synMod)) return;
    markModuleKept(synMod);
    // Syntax macros may expand to anything in the syntax module or its direct project imports
    for (const d of moduleDecls.get(synMod) || []) {
      enqueueTarget(synMod, normalizeQualifiedDeclId(synMod, d), d);
    }
    for (const top of moduleTopRefs.get(synMod) || []) {
      usedModulesByModule.get(synMod)!.add(top.targetModule);
      enqueueTarget(top.targetModule, top.targetId, top.rawName);
    }
    for (const imp of moduleDirectImports.get(synMod) || []) {
      if (syntaxModules.has(imp)) {
        usedModulesByModule.get(synMod)!.add(imp);
        markSyntaxModuleClosure(imp);
      }
    }
  };

  const enqueueTarget = (mod: string, targetId: string, rawName: string) => {
    if (!fileClosure.has(mod)) return;
    markModuleKept(mod);
    const modReach = reachableByModule.get(mod)!;
    modReach.add(targetId);
    modReach.add(rawName);
    const shortSeg = rawName.split(".").pop() || rawName;
    modReach.add(shortSeg);

    const visitKey = `${mod}::${targetId}`;
    if (!visitedDeclKeys.has(visitKey)) {
      visitedDeclKeys.add(visitKey);
      declQueue.push({ mod, declId: targetId, rawName });
    }

    // Match parent declarations for projections/constructors/proof-terms (`Foo.mk` -> `Foo`)
    const knownDecls = moduleDecls.get(mod);
    if (knownDecls) {
      const candidates = [targetId, rawName];
      for (const cand of candidates) {
        const parts = cand.split(".");
        for (let len = parts.length; len >= 1; len--) {
          const prefix = parts.slice(0, len).join(".");
          if (knownDecls.has(prefix)) {
            const qualPrefix = normalizeQualifiedDeclId(mod, prefix);
            modReach.add(prefix);
            modReach.add(qualPrefix);
            const pk = `${mod}::${qualPrefix}`;
            if (!visitedDeclKeys.has(pk)) {
              visitedDeclKeys.add(pk);
              declQueue.push({ mod, declId: qualPrefix, rawName: prefix });
            }
          }
        }
      }
    }
  };

  // Seed `entryModules`: all declarations and all top-level/check references
  for (const em of entryModules) {
    markModuleKept(em);
    for (const d of moduleDecls.get(em) || []) {
      enqueueTarget(em, normalizeQualifiedDeclId(em, d), d);
    }
    for (const top of moduleTopRefs.get(em) || []) {
      usedModulesByModule.get(em)!.add(top.targetModule);
      enqueueTarget(top.targetModule, top.targetId, top.rawName);
    }
  }

  while (declQueue.length > 0) {
    const { mod, declId, rawName } = declQueue.shift()!;
    const lookupKeys = new Set<string>([declId, normalizeQualifiedDeclId(mod, rawName)]);
    for (const lk of lookupKeys) {
      for (const edge of declEdges.get(lk) || []) {
        usedModulesByModule.get(mod)!.add(edge.targetModule);
        enqueueTarget(edge.targetModule, edge.targetId, edge.rawName);
      }
      for (const uMod of declRefModules.get(lk) || []) {
        usedModulesByModule.get(mod)!.add(uMod);
      }
    }
    // Also retain module-level anonymous/instance/command references of `mod` once `mod` is kept:
    // Wait: ONLY follow `moduleTopRefs` if they come from `instance` / anonymous elaborations (`_inst`, etc.),
    // NOT `_check` smoke lines! Note `moduleTopRefs` above pushed `_check` or empty callerRaw;
    // for non-entry modules, `parsedIleans` usages with empty callerRaw are top-level commands/instances.
    if (!entryModules.includes(mod)) {
      const parsed = parsedIleans.get(mod);
      if (parsed?.references) {
        for (const [encKey, refObj] of Object.entries(parsed.references)) {
          const usages = Array.isArray(refObj?.usages) ? refObj.usages : [];
          const hasNonCheckTop = usages.some((u) => !u?.[4]);
          if (!hasNonCheckTop) continue;
          try {
            const cObj = JSON.parse(encKey) as IleanRawRefKey;
            if (cObj?.c?.m && cObj?.c?.n && fileClosure.has(cObj.c.m)) {
              usedModulesByModule.get(mod)!.add(cObj.c.m);
              enqueueTarget(cObj.c.m, normalizeQualifiedDeclId(cObj.c.m, cObj.c.n), cObj.c.n);
            }
          } catch {
            // ignore
          }
        }
      }
    }
  }

  // Also ensure every kept module retains any `instance` declarations' outgoing references!
  // In `.ilean`, `instance` declarations have names like `inst...` in `moduleDecls(mod)`.
  let instChanged = true;
  while (instChanged) {
    instChanged = false;
    for (const mod of Array.from(keptModules)) {
      for (const d of moduleDecls.get(mod) || []) {
        const bare = d.split(".").pop() || d;
        if (/^(?:inst[A-Z0-9_]|default|coe)/.test(bare)) {
          const qid = normalizeQualifiedDeclId(mod, d);
          if (!visitedDeclKeys.has(`${mod}::${qid}`)) {
            enqueueTarget(mod, qid, d);
            instChanged = true;
          }
        }
      }
      while (declQueue.length > 0) {
        const { mod: m2, declId, rawName } = declQueue.shift()!;
        for (const lk of [declId, normalizeQualifiedDeclId(m2, rawName)]) {
          for (const edge of declEdges.get(lk) || []) {
            usedModulesByModule.get(m2)!.add(edge.targetModule);
            enqueueTarget(edge.targetModule, edge.targetId, edge.rawName);
          }
        }
      }
    }
  }

  // Corpus baseline metrics
  const corpusStats = countCorpusLeanFiles(leanRoot, topPrefixes);

  // Compute DAG-preserving imports for each kept module:
  // Keep `directImports(M) ∩ keptModules`, plus promote any `U ∈ usedModulesByModule(M) ∩ keptModules`
  // not transitively reached by `directImports(M) ∩ keptModules`.
  const sortedKeptModules = Array.from(keptModules).sort();
  const keptDirectImports = new Map<string, Set<string>>();
  for (const mod of sortedKeptModules) {
    const set = new Set<string>();
    for (const imp of moduleDirectImports.get(mod) || []) {
      if (keptModules.has(imp) && imp !== mod) set.add(imp);
    }
    keptDirectImports.set(mod, set);
  }

  const reachableViaKeptImports = (startImports: Iterable<string>): Set<string> => {
    const seen = new Set<string>();
    const q = Array.from(startImports);
    while (q.length > 0) {
      const x = q.shift()!;
      if (seen.has(x)) continue;
      seen.add(x);
      for (const nxt of keptDirectImports.get(x) || []) {
        if (!seen.has(nxt)) q.push(nxt);
      }
    }
    return seen;
  };

  // Helper: collect external (`!isProjectModule`, non-`Init`) imports transitively provided by a set of project modules
  const collectTransitiveExternalImports = (seedMods: Iterable<string>): Set<string> => {
    const ext = new Set<string>();
    const seenProj = new Set<string>();
    const q = Array.from(seedMods);
    while (q.length > 0) {
      const m = q.shift()!;
      if (seenProj.has(m)) continue;
      seenProj.add(m);
      for (const imp of moduleDirectImports.get(m) || []) {
        if (isProjectModule(imp)) {
          if (!seenProj.has(imp)) q.push(imp);
        } else if (imp && imp !== "Init" && !imp.startsWith("Init.")) {
          ext.add(imp);
        }
      }
    }
    return ext;
  };

  const moduleOutputs = new Map<string, string>();
  const moduleFullFallbackOutputs = new Map<string, string>();
  const summaries: TreeShakeModuleSummary[] = [];

  let totalLinesAfter = 0;
  let totalBytesAfter = 0;
  let totalPrunedDecls = 0;
  let totalReachableDecls = 0;

  for (const mod of sortedKeptModules) {
    const relPath = moduleSourceRel.get(mod)!;
    const absPath = path.join(leanRoot, relPath);
    const rawSource = fs.readFileSync(absPath, "utf-8");
    const linesBefore = rawSource.split("\n").length;
    const bytesBefore = Buffer.byteLength(rawSource, "utf-8");

    const baseKeptImps = keptDirectImports.get(mod)!;
    const transReached = reachableViaKeptImports(baseKeptImps);
    const promotedProj: string[] = [];
    for (const usedMod of usedModulesByModule.get(mod) || []) {
      if (usedMod !== mod && keptModules.has(usedMod) && !transReached.has(usedMod)) {
        promotedProj.push(usedMod);
      }
    }
    promotedProj.sort();

    // When a direct project import `P` of `mod` is dropped (`!keptModules.has(P)`), preserve external
    // (`Mathlib.*`, `Batteries.*`, `Std.*`, `Cslib.*`) imports that `mod` previously inherited via `P`
    const droppedDirectProj = (moduleDirectImports.get(mod) || []).filter(
      (imp) => isProjectModule(imp) && !keptModules.has(imp)
    );
    const promotedExt: string[] = [];
    if (droppedDirectProj.length > 0) {
      const alreadyProvidedExt = collectTransitiveExternalImports([...baseKeptImps, ...promotedProj]);
      for (const imp of moduleDirectImports.get(mod) || []) {
        if (!isProjectModule(imp)) alreadyProvidedExt.add(imp);
      }
      for (const extImp of collectTransitiveExternalImports(droppedDirectProj)) {
        if (!alreadyProvidedExt.has(extImp)) {
          promotedExt.push(extImp);
        }
      }
      promotedExt.sort();
    }
    const allPromoted = [...promotedExt, ...promotedProj];
    const modAvailableModules = new Set<string>([
      mod,
      ...baseKeptImps,
      ...transReached,
      ...promotedProj,
    ]);
    const isNamespaceUnavailable = (ns: string): boolean => {
      if (!ns.includes(".")) return false;
      const declMods = namespaceToModules.get(ns);
      if (!declMods || declMods.size === 0) return false;
      for (const dm of declMods) {
        if (modAvailableModules.has(dm)) return false;
      }
      return true;
    };
    const isIdentUnavailableInVariable = (ident: string): boolean => {
      const declMods = shortDeclToModules.get(ident);
      if (!declMods || declMods.size === 0) return false;
      for (const dm of declMods) {
        if (modAvailableModules.has(dm)) return false;
      }
      return true;
    };

    // Full-module fallback: anonymize first (preserving byte-0 copyright header match), then rewrite imports
    let fullFallback = anonymize ? anonymizeLeanSource(rawSource) : rawSource;
    fullFallback = rewriteModuleImports(
      fullFallback,
      isProjectModule,
      baseKeptImps,
      allPromoted,
      keptModules,
      isNamespaceUnavailable,
      isIdentUnavailableInVariable
    );
    moduleFullFallbackOutputs.set(mod, fullFallback);

    // IMPORTANT: Prune declaration byte spans on `rawSource` FIRST so `@startByte:endByte` align
    // byte-for-byte with `rawSource`, THEN anonymize & rewrite imports!
    let finalText = fullFallback;
    let keptDeclCount = Math.max(1, Math.floor((moduleDecls.get(mod)?.size ?? 2) / 2));
    let prunedDeclCount = 0;

    if (granularity === "declaration" && !entryModules.includes(mod) && !syntaxModules.has(mod)) {
      const reachSet = reachableByModule.get(mod) || new Set<string>();
      const bareSet = new Set<string>();
      for (const r of reachSet) {
        bareSet.add(r);
        const last = r.split(".").pop();
        if (last) bareSet.add(last);
      }
      const canKeepAttr = (sp: ParsedDeclSpan): boolean => {
        const visitedLocal = new Set<string>();
        const checkDeclCrossModuleClosure = (dName: string, bName: string): boolean => {
          const candKeys = [
            normalizeQualifiedDeclId(mod, dName),
            normalizeQualifiedDeclId(mod, bName),
            dName,
          ];
          for (const ck of candKeys) {
            if (visitedLocal.has(ck)) continue;
            visitedLocal.add(ck);
            const edges = declEdges.get(ck);
            if (!edges) continue;
            for (const edge of edges) {
              if (edge.targetModule === mod) {
                const subBare = edge.targetId.split(".").pop() || edge.targetId;
                if (!checkDeclCrossModuleClosure(edge.targetId, subBare)) {
                  return false;
                }
              } else {
                if (!modAvailableModules.has(edge.targetModule)) return false;
                const tReach = reachableByModule.get(edge.targetModule);
                if (!tReach || !tReach.has(edge.targetId)) {
                  return false;
                }
              }
            }
          }
          return true;
        };
        if (sp.kind === "instance") {
          return checkDeclCrossModuleClosure(sp.name, sp.bareName);
        }
        const topKeys = [
          normalizeQualifiedDeclId(mod, sp.name),
          normalizeQualifiedDeclId(mod, sp.bareName),
          sp.name,
        ];
        const hasAnyEdges = topKeys.some((k) => declEdges.has(k));
        return hasAnyEdges && checkDeclCrossModuleClosure(sp.name, sp.bareName);
      };
      const pruned = pruneModuleDeclarations(
        absPath,
        rawSource,
        bareSet,
        reachSet,
        options.analyzerBin,
        parsedIleans.get(mod)?.decls,
        canKeepAttr
      );
      let rewrittenPruned = anonymize ? anonymizeLeanSource(pruned.prunedText) : pruned.prunedText;
      rewrittenPruned = rewriteModuleImports(
        rewrittenPruned,
        isProjectModule,
        baseKeptImps,
        allPromoted,
        keptModules,
        isNamespaceUnavailable,
        isIdentUnavailableInVariable
      );
      finalText = rewrittenPruned;
      keptDeclCount = pruned.keptCount;
      prunedDeclCount = pruned.prunedCount;
    }

    const linesAfter = finalText.split("\n").length;
    const bytesAfter = Buffer.byteLength(finalText, "utf-8");
    totalLinesAfter += linesAfter;
    totalBytesAfter += bytesAfter;
    totalPrunedDecls += prunedDeclCount;
    totalReachableDecls += keptDeclCount;

    moduleOutputs.set(mod, finalText);
    summaries.push({
      moduleName: mod,
      sourceRelPath: relPath,
      keptDeclarations: keptDeclCount,
      prunedDeclarations: prunedDeclCount,
      linesBefore,
      linesAfter,
      bytesBefore,
      bytesAfter,
      keptImports: Array.from(baseKeptImps).sort(),
      promotedImports: allPromoted,
      fallbackFullModule: false,
    });
  }

  const dryRun = !options.outputDir && !options.archivePath;
  let resolvedOutDir: string | null = options.outputDir ? path.resolve(options.outputDir) : null;
  let tempOutDirCreated = false;
  if (!resolvedOutDir && options.archivePath) {
    resolvedOutDir = fs.mkdtempSync(path.join(os.tmpdir(), "lean-treeshake-"));
    tempOutDirCreated = true;
  }

  let buildVerified = false;
  let buildExitCode: number | null = null;
  let buildLogExcerpt = "";
  let leakHits: TreeShakeLeakHit[] = [];

  if (resolvedOutDir) {
    fs.mkdirSync(resolvedOutDir, { recursive: true });
    for (const [mod, content] of moduleOutputs.entries()) {
      const relPath = moduleSourceRel.get(mod)!;
      const dest = path.join(resolvedOutDir, relPath);
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.writeFileSync(dest, content, "utf-8");
    }

    // Write `lean-toolchain`, `lake-manifest.json`, `lakefile.lean`, and `README.md`
    const tcSrc = path.join(leanRoot, "lean-toolchain");
    if (fs.existsSync(tcSrc)) {
      const rawTc = fs.readFileSync(tcSrc, "utf-8").trim();
      const normalizedTc = /^v4\.\d+\.\d+(?:-[A-Za-z0-9.]+)?$/.test(rawTc)
        ? `leanprover/lean4:${rawTc}\n`
        : `${rawTc}\n`;
      fs.writeFileSync(path.join(resolvedOutDir, "lean-toolchain"), normalizedTc, "utf-8");
    }
    const mfSrc = path.join(leanRoot, "lake-manifest.json");
    const keptTopPrefixes = Array.from(new Set(sortedKeptModules.map((m) => m.split(".")[0]))).sort();
    const pkgName = options.packageName || keptTopPrefixes[0] || "AnonArtifact";
    if (fs.existsSync(mfSrc)) {
      const mfJson = JSON.parse(fs.readFileSync(mfSrc, "utf-8"));
      if (anonymize) {
        mfJson.name = pkgName;
      }
      fs.writeFileSync(path.join(resolvedOutDir, "lake-manifest.json"), JSON.stringify(mfJson, null, 2) + "\n", "utf-8");
    }
    const lf = buildStandaloneLakefile(leanRoot, pkgName, keptTopPrefixes, anonymize);
    fs.writeFileSync(path.join(resolvedOutDir, lf.filename), lf.content, "utf-8");

    const readmeLines = [
      `# Machine-Checked Lean 4 Formalization Artifact`,
      ``,
      anonymize
        ? `Anonymized standalone supplementary slice generated by declaration-level tree-shaking for double-blind peer review.`
        : `Standalone Lean 4 slice generated by \`lean-tree-shake\`.`,
      ``,
      `## Entry Module(s)`,
      ...entryModules.map((m) => `- \`${m}\``),
      ``,
      `## Standalone Verification`,
      `\`\`\`bash`,
      `lake exe cache get   # optional: download prebuilt Mathlib .olean cache`,
      `lake build ${entryModules.join(" ")}`,
      `\`\`\``,
      ``,
    ];
    fs.writeFileSync(path.join(resolvedOutDir, "README.md"), readmeLines.join("\n"), "utf-8");

    // Optional kernel build verification (reusing pre-fetched `.lake/packages` symlink so offline sandbox / fast verification works, then unlinking `.lake` before tar!)
    if (options.verifyBuild) {
      const origPackages = path.join(leanRoot, ".lake", "packages");
      const outLakeDir = path.join(resolvedOutDir, ".lake");
      const outPackages = path.join(outLakeDir, "packages");
      let createdPackagesLink = false;
      if (
        options.symlinkLakePackagesForVerify !== false &&
        fs.existsSync(origPackages) &&
        !fs.existsSync(outPackages)
      ) {
        fs.mkdirSync(outLakeDir, { recursive: true });
        fs.symlinkSync(origPackages, outPackages, "dir");
        createdPackagesLink = true;
      }

      const timeoutMs = options.timeoutMs ?? 600000;
      // Up to 4 self-healing rounds: if a pruned module had a macro-hidden dependency, restore that module's full import-pruned body!
      for (let attempt = 0; attempt < 4; attempt++) {
        const res = await runLakeBuildAsync(resolvedOutDir, entryModules, timeoutMs);
        buildExitCode = res.exitCode;
        buildLogExcerpt = res.output.split("\n").slice(-35).join("\n");
        if (res.exitCode === 0) {
          buildVerified = true;
          break;
        }
        // Parse failing `.lean` relative paths from Lake output (`error: MyProject/Foo.lean:40:15:` or `./MyProject/Foo.lean:...`)
        const errFileRe = /(?:error:\s*|\s|\.)\/?([A-Za-z0-9_]+(?:\/[A-Za-z0-9_']+)+\.lean):\d+:\d+:/gm;
        const failedMods = new Set<string>();
        let em: RegExpExecArray | null;
        while ((em = errFileRe.exec(res.output)) !== null) {
          const modName = em[1].replace(/\.lean$/, "").replace(/\//g, ".");
          if (moduleFullFallbackOutputs.has(modName)) {
            failedMods.add(modName);
          }
        }
        let restoredAny = false;
        for (const fm of failedMods) {
          const sum = summaries.find((s) => s.moduleName === fm);
          if (sum && !sum.fallbackFullModule) {
            const fullTxt = moduleFullFallbackOutputs.get(fm)!;
            fs.writeFileSync(path.join(resolvedOutDir, moduleSourceRel.get(fm)!), fullTxt, "utf-8");
            totalLinesAfter += sum.linesBefore - sum.linesAfter;
            totalBytesAfter += sum.bytesBefore - sum.bytesAfter;
            totalPrunedDecls -= sum.prunedDeclarations;
            sum.linesAfter = sum.linesBefore;
            sum.bytesAfter = sum.bytesBefore;
            sum.prunedDeclarations = 0;
            sum.fallbackFullModule = true;
            restoredAny = true;
          }
        }
        if (!restoredAny) break;
      }

      if (createdPackagesLink && options.archivePath) {
        // Remove `.lake` build artifacts & symlink before archiving so the `.tar.gz` is a pure, lightweight source archive!
        fs.rmSync(outLakeDir, { recursive: true, force: true });
      }
    }

    // Run anonymity leak check across all emitted source files
    const autoPatterns = new Set<string>(options.forbiddenPatterns || []);
    if (anonymize) {
      const user = os.userInfo().username;
      if (user && user.length >= 3 && user !== "root" && user !== "runner") {
        autoPatterns.add(user);
      }
    }
    leakHits = scanDirectoryForIdentityLeaks(resolvedOutDir, Array.from(autoPatterns));

    if (options.archivePath) {
      const absArchive = path.resolve(options.archivePath);
      fs.mkdirSync(path.dirname(absArchive), { recursive: true });
      // Exclude `.lake` defensively and strip all UID/GID/mtime host metadata
      const tarRes = spawnSync(
        "tar",
        [
          "--exclude=.lake",
          "--exclude=.git",
          "--sort=name",
          "--mtime=UTC 2026-01-01",
          "--owner=0",
          "--group=0",
          "--numeric-owner",
          "-czf",
          absArchive,
          "-C",
          resolvedOutDir,
          ".",
        ],
        { encoding: "utf-8" }
      );
      if (tarRes.status !== 0) {
        // Portable BSD/macOS tar fallback if GNU `--sort=name` / `--mtime` is unsupported
        const fallbackTar = spawnSync(
          "tar",
          ["--exclude=.lake", "--exclude=.git", "-czf", absArchive, "-C", resolvedOutDir, "."],
          { encoding: "utf-8" }
        );
        if (fallbackTar.status !== 0) {
          throw new Error(`Failed to create archive ${absArchive}: ${fallbackTar.stderr || tarRes.stderr}`);
        }
      }
    }

    if (tempOutDirCreated) {
      fs.rmSync(resolvedOutDir, { recursive: true, force: true });
      resolvedOutDir = null;
    }
  }

  const lineReductionPct =
    corpusStats.lines > 0 ? ((corpusStats.lines - totalLinesAfter) / corpusStats.lines) * 100 : 0;
  const byteReductionPct =
    corpusStats.bytes > 0 ? ((corpusStats.bytes - totalBytesAfter) / corpusStats.bytes) * 100 : 0;

  return {
    schemaVersion: 1,
    leanRoot,
    entryModules,
    granularity,
    dryRun,
    outputDir: resolvedOutDir,
    archivePath: options.archivePath ? path.resolve(options.archivePath) : null,
    anonymized: anonymize,
    totalCorpusModules: corpusStats.files,
    fileImportClosureModules: fileClosure.size,
    keptModulesCount: sortedKeptModules.length,
    reachableDeclarationsCount: totalReachableDecls,
    prunedDeclarationsCount: totalPrunedDecls,
    totalLinesBefore: corpusStats.lines,
    totalLinesAfter,
    lineReductionPct,
    totalBytesBefore: corpusStats.bytes,
    totalBytesAfter,
    byteReductionPct,
    anonymityLeakHits: leakHits,
    buildVerified,
    buildExitCode,
    buildLogExcerpt,
    modules: summaries,
  };
}
