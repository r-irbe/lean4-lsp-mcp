// src/tree_shake.ts
// Declaration-level and module-level Lean 4 tree-shaker powered by offline
// `.ilean` reference graphs and `lean-analyzer parse --spans` UTF-8 byte spans.
// Emits standalone, kernel-verifiable, optionally anonymized Lake slices and `.tar.gz` archives.
// Scoped Unicode policy (INV-001; typographic-free by default).

import { spawn, spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as zlib from "node:zlib";
import { stripLeanCommentsAndStrings } from "./lean_source.ts";
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
  kind: "theorem" | "lemma" | "def" | "abbrev" | "structure" | "class" | "inductive" | "instance" | "example";
  name: string;
  bareName: string;
  startByte: number;
  endByte: number;
  hasGlobalAttr: boolean;
  isDeprecated: boolean;
  headText: string;
  rawText: string;
}

const GLOBAL_KEEP_ATTR_RE =
  /@\[[^\]]*\b(?:simp|ext|aesop|norm_cast|push_cast|coe|csimp|reducible|semireducible|default_instance|instance|elab_as_elim|lia|positivity|fun_prop|continuity|measurability|gcongr)\b[^\]]*\]/;

const DEPRECATED_ATTR_RE = /@\[[^\]]*\bdeprecated\b[^\]]*\]/;

/** Extract the declaration header/signature prior to `:=` or `where` (outside comments/strings). */
function extractDeclSignatureHead(codeNoComments: string): string {
  const trimmed = codeNoComments.trimStart();
  const whereMatch = trimmed.search(/\bwhere\b|:=|\|/);
  if (whereMatch > 0) {
    return trimmed.slice(0, whereMatch);
  }
  return trimmed.slice(0, 600);
}

const NOTATION_PROVIDER_RE =
  /^\s*(?:scoped\s+)?(?:notation|infix|infixl|infixr|prefix|postfix)\b/m;

const TACTIC_SYNTAX_PROVIDER_RE =
  /^\s*(?:scoped\s+)?(?:macro|macro_rules|elab|elab_rules|syntax|register_simp_attr)\b/m;

const EXTERNAL_OR_CACHE_PACKAGE_NAMES = new Set<string>([
  "mathlib",
  "batteries",
  "Qq",
  "aesop",
  "proofwidgets",
  "importGraph",
  "LeanSearchClient",
  "plausible",
  "cslib",
  "Cli",
  "LSpec",
]);

/** Discover local first-party path packages (`"type": "path"`) from `<leanRoot>/lake-manifest.json`. */
function discoverLocalPathPackageDirs(leanRoot: string): string[] {
  const mfPath = path.join(leanRoot, "lake-manifest.json");
  if (!fs.existsSync(mfPath)) return [];
  const out: string[] = [];
  try {
    const mf = JSON.parse(fs.readFileSync(mfPath, "utf-8"));
    for (const pkg of mf.packages || []) {
      if (
        pkg &&
        pkg.type === "path" &&
        typeof pkg.dir === "string" &&
        typeof pkg.name === "string" &&
        !EXTERNAL_OR_CACHE_PACKAGE_NAMES.has(pkg.name)
      ) {
        const resolved = path.resolve(leanRoot, pkg.dir);
        if (resolved !== leanRoot && fs.existsSync(resolved)) {
          out.push(resolved);
        }
      }
    }
  } catch {
    // ignore malformed manifest
  }
  return out;
}

export interface ModuleSyntaxBlock {
  kind: "syntax" | "macro" | "macro_rules" | "elab" | "elab_rules" | "register_simp_attr";
  keywords: string[];
  synIdent: string;
  bodyText: string;
  startLine: number;
  endLine: number;
}

export interface ModuleSyntaxAnalysis {
  blocks: ModuleSyntaxBlock[];
  /** Map from `synIdent` (e.g. `finsetNonnegTactic`) to `@[tactic synIdent] def <fnName>` */
  tacticAttrEvaluators: Map<string, string[]>;
  /** All distinct custom surface keywords declared in this module */
  allKeywords: Set<string>;
}

function extractKeywordsFromSyntaxHeader(headerText: string): string[] {
  const kws: string[] = [];
  const strRe = /"([^"]+)"/g;
  let m: RegExpExecArray | null;
  while ((m = strRe.exec(headerText)) !== null) {
    const trimmed = m[1].trim();
    // Keep genuine tactic/command/elaborator surface keywords (`sum_congr_ring`, `elegance?`, `eval_nat%`, `#p2m_type_eq`);
    // skip structural punctuation literals (`[`, `]`, `,`, `for`, `from`, `via`, `then` after primary keyword).
    if (!trimmed) continue;
    if (!/^[#A-Za-z_][A-Za-z0-9_'?%]*$/.test(trimmed)) continue;
    if (kws.length > 0 && /^(?:for|from|via|then|with|using|in|at|to|by)$/.test(trimmed)) {
      continue;
    }
    if (!kws.includes(trimmed)) {
      kws.push(trimmed);
    }
  }
  return kws;
}

function extractKeywordsFromMacroRules(blockText: string): string[] {
  const kws: string[] = [];
  // Match `` `(tactic| foo_bar... `` or `` `(command| foo_bar... `` or `` `(term| foo_bar... ``
  const armRe = /`\(\s*(?:[A-Za-z0-9_.']+\s*\|\s*)?([#A-Za-z_][A-Za-z0-9_'?%]*)/g;
  let m: RegExpExecArray | null;
  // Only inspect LHS arms before `=>`
  for (const line of blockText.split("\n")) {
    const trimmed = line.trimStart();
    if (!trimmed.startsWith("|")) continue;
    const arrowIdx = trimmed.indexOf("=>");
    const lhs = arrowIdx >= 0 ? trimmed.slice(0, arrowIdx) : trimmed;
    armRe.lastIndex = 0;
    while ((m = armRe.exec(lhs)) !== null) {
      const kw = m[1].trim();
      if (kw && !kws.includes(kw)) {
        kws.push(kw);
      }
    }
  }
  return kws;
}

/** Parse top-level `syntax` / `macro` / `macro_rules` / `elab` / `register_simp_attr` blocks and `@[tactic ...]` evaluators. */
export function analyzeModuleSyntax(sourceText: string): ModuleSyntaxAnalysis {
  const lines = sourceText.split("\n");
  const blocks: ModuleSyntaxBlock[] = [];
  const allKeywords = new Set<string>();
  const tacticAttrEvaluators = new Map<string, string[]>();

  // Scan `@[tactic foo, tactic bar] def evalBaz`
  const noComments = stripLeanCommentsAndStrings(sourceText);
  const attrRe = /@\[([^\]]+)\]\s*(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+)*def\s+([A-Za-z_][A-Za-z0-9_']*)/g;
  let am: RegExpExecArray | null;
  while ((am = attrRe.exec(noComments)) !== null) {
    const attrInside = am[1];
    const fnName = am[2];
    const tacRe = /\btactic\s+([A-Za-z_][A-Za-z0-9_.']*)/g;
    let tm: RegExpExecArray | null;
    while ((tm = tacRe.exec(attrInside)) !== null) {
      const synId = tm[1].split(".").pop()!;
      let list = tacticAttrEvaluators.get(synId);
      if (!list) {
        list = [];
        tacticAttrEvaluators.set(synId, list);
      }
      if (!list.includes(fnName)) list.push(fnName);
    }
  }

  let i = 0;
  let inBlockComment = 0;
  while (i < lines.length) {
    const rawLine = lines[i];
    // Track top-level block comments so `/-- ... -/` or `/-! ... -/` interiors are never mistaken for column-0 commands
    let lineScan = 0;
    const prevCommentDepth = inBlockComment;
    while (lineScan < rawLine.length - 1) {
      if (inBlockComment === 0 && rawLine[lineScan] === "-" && rawLine[lineScan + 1] === "-") break;
      if (rawLine[lineScan] === "/" && rawLine[lineScan + 1] === "-") {
        inBlockComment++;
        lineScan += 2;
        continue;
      }
      if (inBlockComment > 0 && rawLine[lineScan] === "-" && rawLine[lineScan + 1] === "/") {
        inBlockComment--;
        lineScan += 2;
        continue;
      }
      lineScan++;
    }
    if (prevCommentDepth > 0 || inBlockComment > 0) {
      i++;
      continue;
    }

    const cmdMatch = rawLine.match(/^(?:scoped\s+)?(syntax|macro_rules|macro|elab_rules|elab|register_simp_attr)\b/);
    if (!cmdMatch) {
      i++;
      continue;
    }
    const kind = cmdMatch[1] as ModuleSyntaxBlock["kind"];
    let docStart = i;
    if (i > 0 && lines[i - 1].trimEnd().endsWith("-/")) {
      let d = i - 1;
      while (d >= 0) {
        if (lines[d].trimStart().startsWith("/--")) {
          docStart = d;
          break;
        }
        if (lines[d].trimStart().startsWith("/-")) break;
        d--;
      }
    }
    let endLine = i;
    while (endLine + 1 < lines.length) {
      const nxt = lines[endLine + 1];
      if (nxt.trim() === "") {
        // Look ahead to see if next non-empty line is indented continuation
        let peek = endLine + 2;
        while (peek < lines.length && lines[peek].trim() === "") peek++;
        if (peek < lines.length && /^[ \t]+/.test(lines[peek])) {
          endLine = peek;
          continue;
        }
        break;
      }
      if (/^[ \t]+/.test(nxt)) {
        endLine++;
        continue;
      }
      break;
    }
    const cmdText = lines.slice(i, endLine + 1).join("\n");
    let synIdent = "";
    const nameMatch = cmdText.match(/\(\s*name\s*:=\s*([A-Za-z_][A-Za-z0-9_']*)\s*\)/);
    if (nameMatch) {
      synIdent = nameMatch[1];
    }
    let keywords: string[] = [];
    if (kind === "register_simp_attr") {
      const rsaMatch = cmdText.match(/\bregister_simp_attr\s+([A-Za-z_][A-Za-z0-9_']*)/);
      if (rsaMatch) keywords = [rsaMatch[1]];
    } else if (kind === "macro_rules" || kind === "elab_rules") {
      keywords = extractKeywordsFromMacroRules(cmdText);
    } else {
      const arrowIdx = cmdText.indexOf("=>");
      const headerPart = arrowIdx >= 0 ? cmdText.slice(0, arrowIdx) : cmdText;
      keywords = extractKeywordsFromSyntaxHeader(headerPart);
    }
    for (const kw of keywords) allKeywords.add(kw);
    // Extract RHS body text (for `macro_rules`, `macro`, `elab`) so nested tactic calls can be traced
    let bodyText = "";
    if (kind === "macro_rules" || kind === "elab_rules") {
      bodyText = cmdText
        .split("\n")
        .map((ln) => {
          const idx = ln.indexOf("=>");
          return idx >= 0 ? ln.slice(idx + 2) : ln.trimStart().startsWith("|") ? "" : ln;
        })
        .join("\n");
    } else if (kind !== "register_simp_attr") {
      const idx = cmdText.indexOf("=>");
      bodyText = idx >= 0 ? cmdText.slice(idx + 2) : "";
    }
    blocks.push({
      kind,
      keywords,
      synIdent,
      bodyText,
      startLine: docStart,
      endLine,
    });
    i = endLine + 1;
  }

  return { blocks, tacticAttrEvaluators, allKeywords };
}

/** Check whether `codeNoComments` invokes surface syntax keyword `kw` (handling leading `#` and trailing `?` or `%`). */
export function codeContainsSurfaceKeyword(codeNoComments: string, kw: string): boolean {
  if (!kw) return false;
  let pos = codeNoComments.indexOf(kw);
  while (pos !== -1) {
    const prev = pos > 0 ? codeNoComments[pos - 1] : "";
    const next = pos + kw.length < codeNoComments.length ? codeNoComments[pos + kw.length] : "";
    const prevIsIdent = /[#A-Za-z0-9_']/.test(prev);
    const nextIsIdentOrSuffix = /[A-Za-z0-9_'?%]/.test(next);
    if (!prevIsIdent && !nextIsIdentOrSuffix) {
      return true;
    }
    pos = codeNoComments.indexOf(kw, pos + 1);
  }
  return false;
}

/**
 * Strip unused top-level `syntax` / `macro` / `macro_rules` / `elab` / `register_simp_attr` blocks
 * (and any column-0 self-smoke command calls to dropped command macros) from a pruned syntax-provider module.
 */
export function stripUnusedSyntaxBlocks(
  sourceText: string,
  activeKeywords: ReadonlySet<string>
): string {
  const analysis = analyzeModuleSyntax(sourceText);
  if (analysis.blocks.length === 0) return sourceText;
  const lines = sourceText.split("\n");
  const dropLine = new Uint8Array(lines.length);
  const droppedKeywords = new Set<string>();

  for (const blk of analysis.blocks) {
    if (blk.keywords.length === 0) continue;
    const isActive = blk.keywords.some((kw) => activeKeywords.has(kw));
    if (!isActive) {
      for (let l = blk.startLine; l <= blk.endLine && l < lines.length; l++) {
        dropLine[l] = 1;
      }
      for (const kw of blk.keywords) droppedKeywords.add(kw);
    }
  }

  // Also strip any column-0 command macro invocations (`<droppedKw> ...`) left in the file (e.g. smoke tests)
  if (droppedKeywords.size > 0) {
    let i = 0;
    while (i < lines.length) {
      if (dropLine[i]) {
        i++;
        continue;
      }
      const m = lines[i].match(/^([#A-Za-z_][A-Za-z0-9_'?%]*)\b/);
      if (m && droppedKeywords.has(m[1])) {
        let end = i;
        while (end + 1 < lines.length && /^[ \t]+/.test(lines[end + 1])) {
          end++;
        }
        for (let l = i; l <= end; l++) dropLine[l] = 1;
        i = end + 1;
        continue;
      }
      i++;
    }
  }

  return lines.filter((_, idx) => !dropLine[idx]).join("\n");
}

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

/** Collect all `.ilean` files under `<root>/.lake/build/lib/lean` (or `<root>/.lake/build/lib`) across project and local path packages. */
function collectProjectIleanFiles(leanRoot: string, extraRoots: readonly string[] = []): string[] {
  const out: string[] = [];
  const seenFiles = new Set<string>();
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
        const real = fs.existsSync(full) ? fs.realpathSync(full) : full;
        if (!seenFiles.has(real)) {
          seenFiles.add(real);
          out.push(full);
        }
      }
    }
  };
  for (const root of [leanRoot, ...extraRoots]) {
    const candidates = [
      path.join(root, ".lake", "build", "lib", "lean"),
      path.join(root, ".lake", "build", "lib"),
    ];
    for (const c of candidates) {
      if (fs.existsSync(c)) {
        walk(c);
        break;
      }
    }
  }
  return out;
}

/** Count all `.lean` source files belonging to the primary project prefixes (e.g. `MyProject/`). */
function countCorpusLeanFiles(
  leanRoot: string,
  topPrefixes: Set<string>,
  extraRoots: readonly string[] = []
): { files: number; lines: number; bytes: number } {
  let files = 0;
  let lines = 0;
  let bytes = 0;
  const seenReal = new Set<string>();
  const recordFile = (full: string) => {
    try {
      const real = fs.realpathSync(full);
      if (seenReal.has(real)) return;
      seenReal.add(real);
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
  };
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
        recordFile(full);
      }
    }
  };
  for (const root of [leanRoot, ...extraRoots]) {
    for (const pref of topPrefixes) {
      const topFile = path.join(root, `${pref}.lean`);
      if (fs.existsSync(topFile)) {
        recordFile(topFile);
      }
      const topDir = path.join(root, pref);
      if (fs.existsSync(topDir)) walk(topDir);
    }
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
  // Match top-level `(theorem|lemma|def|abbrev|structure|class|inductive|example [l0, c0] - [l1, c1] @b0:b1 ...)`
  const headerRe =
    /\((theorem|lemma|def|abbrev|structure|class|inductive|example)\s+\[(\d+),\s*(\d+)\]\s*-\s*\[(\d+),\s*(\d+)\]\s*@(\d+):(\d+)/g;
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
    const isDeprecated = DEPRECATED_ATTR_RE.test(codeNoComments.slice(0, 600));
    const hasGlobalAttr =
      !isDeprecated &&
      kind !== "structure" &&
      kind !== "class" &&
      kind !== "inductive" &&
      GLOBAL_KEEP_ATTR_RE.test(codeNoComments.slice(0, 600));
    spans.push({
      kind,
      name,
      bareName,
      startByte,
      endByte: adjEndByte,
      hasGlobalAttr,
      isDeprecated,
      headText: extractDeclSignatureHead(codeNoComments),
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
    const finalDeprecated = DEPRECATED_ATTR_RE.test(finalNoComments.slice(0, 600));
    clean.push({
      ...sp,
      startByte: adjStart,
      isDeprecated: finalDeprecated,
      hasGlobalAttr:
        !finalDeprecated &&
        sp.kind !== "structure" &&
        sp.kind !== "class" &&
        sp.kind !== "inductive" &&
        GLOBAL_KEEP_ATTR_RE.test(finalNoComments.slice(0, 600)),
      headText: extractDeclSignatureHead(finalNoComments),
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
  const coveredLines = new Uint8Array(srcLines.length);
  for (const [rawDeclName, coords] of Object.entries(ileanDecls)) {
    if (!Array.isArray(coords) || coords.length < 4) continue;
    const [sL, sC, eL, eC] = coords;
    if (sC < 0 || sL < 0 || eL < sL || eL >= srcLines.length) continue;
    const startByte = toByte(sL, sC);
    let endByte = toByte(eL, eC);
    // Include any trailing `-- ...` inline comment on `endLine` so pruning never orphans trailing comments
    const clampedEC = Math.max(0, Math.min(srcLines[eL].length, eC));
    const restOfEndLine = srcLines[eL].slice(clampedEC);
    if (restOfEndLine.length > 0 && /^[ \t]*--/.test(restOfEndLine)) {
      endByte = toByte(eL, srcLines[eL].length);
    }
    if (endByte <= startByte || endByte > sourceBuf.length) continue;

    const rawText = sourceBuf.subarray(startByte, endByte).toString("utf-8");
    const codeNoComments = stripLeanCommentsAndStrings(rawText).trimStart();
    const codeHead = codeNoComments.slice(0, 1200);
    const kwMatch = codeHead.match(
      /^\s*(?:@\[[^\]]*\]\s*|(?:\b(?:private|protected|noncomputable|partial|unsafe|scoped|local)\b)\s*)*(theorem|lemma|def|abbrev|structure|class|inductive|instance)\b/
    );
    if (!kwMatch) continue;
    for (let l = sL; l <= eL; l++) coveredLines[l] = 1;
    const kind = kwMatch[1] as ParsedDeclSpan["kind"];
    const cleanName = rawDeclName.startsWith("_private.")
      ? rawDeclName.split(".").pop() || rawDeclName
      : rawDeclName;
    const bareName = cleanName.includes(".") ? cleanName.split(".").pop()! : cleanName;
    const isDeprecated = DEPRECATED_ATTR_RE.test(codeHead.slice(0, 600));
    const hasGlobalAttr =
      !isDeprecated &&
      (kind === "instance" ||
        (kind !== "structure" &&
          kind !== "class" &&
          kind !== "inductive" &&
          GLOBAL_KEEP_ATTR_RE.test(codeHead.slice(0, 600))));
    rawSpans.push({
      kind,
      name: cleanName,
      bareName,
      startByte,
      endByte,
      hasGlobalAttr,
      isDeprecated,
      headText: extractDeclSignatureHead(codeNoComments),
      rawText,
    });
  }

  // Also capture anonymous column-0 `example ...` blocks AND 0-binder ground declarations omitted from `.ilean` `decls`
  let scanCommentDepth = 0;
  for (let i = 0; i < srcLines.length; i++) {
    const rawLine = srcLines[i];
    const prevDepth = scanCommentDepth;
    for (let c = 0; c < rawLine.length - 1; c++) {
      if (scanCommentDepth === 0 && rawLine[c] === "-" && rawLine[c + 1] === "-") break;
      if (rawLine[c] === "/" && rawLine[c + 1] === "-") {
        scanCommentDepth++;
        c++;
      } else if (scanCommentDepth > 0 && rawLine[c] === "-" && rawLine[c + 1] === "/") {
        scanCommentDepth--;
        c++;
      }
    }
    if (prevDepth > 0 || scanCommentDepth > 0 || coveredLines[i]) continue;

    const topMatch = rawLine.match(
      /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(example|(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_.']*))\b/
    );
    if (topMatch) {
      const isExample = topMatch[1] === "example";
      const declKind = (isExample ? "example" : topMatch[2]) as ParsedDeclSpan["kind"];
      const declName = isExample ? "(example)" : topMatch[3];
      const declBare = isExample ? "(example)" : declName.split(".").pop() || declName;

      let exStartLine = i;
      // Include attached `/-- ... -/` doc comment immediately above declaration
      if (i > 0 && !coveredLines[i - 1] && srcLines[i - 1].trimEnd().endsWith("-/")) {
        let d = i - 1;
        while (d >= 0 && !coveredLines[d]) {
          if (srcLines[d].trimStart().startsWith("/--")) {
            exStartLine = d;
            break;
          }
          if (srcLines[d].trimStart().startsWith("/-")) break;
          d--;
        }
      }
      let exEndLine = i;
      while (exEndLine + 1 < srcLines.length && !coveredLines[exEndLine + 1]) {
        const nxt = srcLines[exEndLine + 1];
        if (nxt.trim() === "") {
          let peek = exEndLine + 2;
          while (peek < srcLines.length && srcLines[peek].trim() === "") peek++;
          if (peek < srcLines.length && !coveredLines[peek] && /^[ \t]+/.test(srcLines[peek])) {
            exEndLine = peek;
            continue;
          }
          break;
        }
        if (/^[ \t]+/.test(nxt)) {
          exEndLine++;
          continue;
        }
        break;
      }
      const startByte = lineStartByte[exStartLine];
      const endByte = toByte(exEndLine, srcLines[exEndLine].length);
      if (endByte > startByte) {
        const exRaw = sourceBuf.subarray(startByte, endByte).toString("utf-8");
        const exNoComments = stripLeanCommentsAndStrings(exRaw).trimStart();
        const exDeprecated = !isExample && DEPRECATED_ATTR_RE.test(exNoComments.slice(0, 600));
        const exGlobal = !isExample && !exDeprecated && GLOBAL_KEEP_ATTR_RE.test(exNoComments.slice(0, 600));
        rawSpans.push({
          kind: declKind,
          name: declName,
          bareName: declBare,
          startByte,
          endByte,
          hasGlobalAttr: exGlobal,
          isDeprecated: exDeprecated,
          headText: isExample ? "" : extractDeclSignatureHead(exNoComments),
          rawText: exRaw,
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

export interface AnonymizeLeanOptions {
  ensureLicenseHeader?: boolean;
  keptModuleNames?: ReadonlySet<string>;
  keptModuleBaseNames?: ReadonlySet<string>;
}

function scrubCommentChunkForAnonymity(
  commentText: string,
  options?: AnonymizeLeanOptions
): string {
  let c = commentText;
  // INV-001 typographic hygiene inside comments (never touching Lean code tokens)
  c = c.replace(/\u2500/g, "-");
  c = c.replace(/[\u2013\u2014]/g, "--");
  c = c.replace(/[\u2018\u2019]/g, "'");
  c = c.replace(/[\u201C\u201D]/g, '"');
  c = c.replace(/\u2026/g, "...");
  c = c.replace(/[\u00A0\u202F\u2009\u2007\u2002\u2003\u2004]/g, " ");
  c = c.replace(/\u27FA/g, "<=>");
  c = c.replace(/\u27F9/g, "=>");
  c = c.replace(/\u2033/g, "''");
  c = c.replace(/\u2032/g, "'");

  // 1. Replace full backticked internal repo/docs/submodule paths FIRST so filename rules never split mid-path
  c = c.replace(
    /`(?:docs|lean|playbooks|wave-\d+|packages|\.agents|\.github|skills|tools)\/[^`\n]+`(?:\s*§[0-9A-Za-z.+-]+)?/g,
    "the companion specification"
  );
  c = c.replace(
    /\b(?:docs|lean\/report|playbooks|wave-\d+)\/[A-Za-z0-9_./:-]+/g,
    "the companion specification"
  );

  // 2. Scrub internal manuscript, playbook, report-chapter, and zettelkasten tags (100% project-agnostic)
  c = c.replace(/`?(?:docs\/presentations\/)?[A-Z0-9_]+_PLAN\.md`?/g, "the formalization design notes");
  c = c.replace(/`?[A-Za-z0-9_-]+\.tex(?:\s*\/\s*`?[A-Za-z0-9_-]+\.tex`?)?`?/g, "the companion paper");
  c = c.replace(/\bAppendix\s+[A-Z]\s*(?:\([^()\n]*\)\s*)?of\s+the\s+[A-Za-z0-9_-]+\s+paper\b/gi, "the companion specification");
  c = c.replace(/\bSection\s+\d+\s+of\s+the\s+[A-Za-z0-9_-]+\s+paper\s*(?:\([^()\n]*\))?/gi, "the companion specification");
  c = c.replace(/\bReport\s+Chapter\s+\d+(?:,\s*§§?[0-9\-\u2013]+)?/gi, "the companion specification");
  c = c.replace(/\bChapter\s+\d+\s+of\s+the\s+report\b/gi, "the companion specification");
  c = c.replace(/\bChapter\s+\d+,\s*§§?[0-9\-\u2013]+/gi, "the companion specification");
  c = c.replace(/\bzet-book-[A-Za-z0-9_-]+\b/g, "standard Markov-chain reference");

  // 3. Scrub leading docstring ticket prefixes `/-- (W57) ` and parenthetical/bracketed campaign/HITL/audit tags
  c = c.replace(
    /^(\/--\s*)\(\s*(?:W\d+[^)\n]*|(?:REC|CN|MS|LG|FG|G)-\d+[^)\n]*)\)\s*/gm,
    "$1"
  );
  c = c.replace(
    /[ \t]*\(\s*(?:[^()\n]*\b(?:W\d+(?:[-/][A-Za-z0-9_~+.]+)?|HITL|REC-\d+|CN-\d+|MS-\d+|LG-\d+|FG-\d+|TAUT-\d+)\b[^()\n]*)\)/g,
    ""
  );
  c = c.replace(
    /[ \t]*\[\s*(?:[^\[\]\n]*\b(?:W\d+(?:[-/][A-Za-z0-9_~+.]+)?|HITL|REC-\d+|CN-\d+|MS-\d+|LG-\d+|FG-\d+|TAUT-\d+)\b[^\[\]\n]*)\]/g,
    ""
  );
  // Phrase-level campaign-scaffoldingclauses so stripping `W\d+` never leaves broken sentences (`split out in .`, `per the  prep`, `Made public during `)
  c = c.replace(/;\s*split\s+out\s+in\s+W\d+[A-Za-z0-9_/-]*/gi, "");
  c = c.replace(/\bper\s+the\s+W\d+[A-Za-z0-9_/-]*\s+prep\s+recipe\s+step\s+\d+/gi, "for modular reuse");
  c = c.replace(/\bpending\s+W\d+[A-Za-z0-9_/-]*\s+main\s+migration/gi, "in the main facade");
  c = c.replace(/\bof\s+the\s+W\d+[A-Za-z0-9_/-]*\s+deferral\b/gi, "of the deferred obligation");
  c = c.replace(/\bMade\s+public\s+during\s+W\d+[A-Za-z0-9_/-]*\s+because\b/gi, "Exposed publicly because");
  c = c.replace(/\bused\s+by\s+the\s+W\d+\s+tensor\s+slice,\s*`?TensorNetwork\.PathGate`?/gi, "for finite enumeration");
  c = c.replace(/\bused\s+by\s+W\d+\s+§[0-9a-zA-Z\-\u00a7]+\s+/g, "used by the ");
  c = c.replace(/\bHITL(?:\s+choice)?\s+[A-Za-z0-9_~+-]+/g, "");
  c = c.replace(/\bW\d+(?:[-/][A-Za-z0-9_~+.]+)?\b/g, "");
  c = c.replace(/\b(?:REC|CN|MS|LG|FG|TAUT)-\d+\b/g, "");
  c = c.replace(/\bWave[- ]\d+\b/gi, "refactor pass");
  c = c.replace(/\bRoute\s+B'+/g, "Alternative route");
  c = c.replace(/\bRoute\s+B\b/g, "Topological route");
  c = c.replace(/\bWRAP\s+playbook\b/gi, "bridge specification");
  c = c.replace(/\bOVERVIEW\.md\b/g, "module overview");
  c = c.replace(/\bAGENTS\.md\b/g, "project guidelines");

  // 4. Scrub explicit `:line` pointers into unshipped internal `.lean:NN` files (without mangling Mathlib paths or prose)
  if (options?.keptModuleBaseNames && options.keptModuleBaseNames.size > 0) {
    const keptBases = options.keptModuleBaseNames;
    c = c.replace(/`([A-Za-z0-9_/]+\.lean):\d+`/g, (full, relLean: string) => {
      const base = relLean.split("/").pop() || relLean;
      return keptBases.has(base) ? `\`${relLean}\`` : "a companion module";
    });
  }

  // 5. Tidy spacing scars inside comment lines without altering leading indentation
  c = c
    .split("\n")
    .map((ln) => {
      const indentMatch = ln.match(/^([ \t]*)(.*)$/);
      if (!indentMatch) return ln;
      const [, indent, rest] = indentMatch;
      const cleaned = rest
        .replace(/\(\s*\)/g, "")
        .replace(/\[\s*\]/g, "")
        .replace(/[ \t]+([,.;:)])/g, "$1")
        .replace(/ {2,}/g, " ")
        .trimEnd();
      return cleaned ? `${indent}${cleaned}` : "";
    })
    .join("\n");
  return c;
}

function transformLeanCommentsOnly(src: string, fn: (comment: string) => string): string {
  const out: string[] = [];
  let i = 0;
  const n = src.length;
  while (i < n) {
    const ch = src[i];
    const nxt = i + 1 < n ? src[i + 1] : "";
    if (ch === "/" && nxt === "-") {
      const start = i;
      let depth = 1;
      i += 2;
      while (i < n && depth > 0) {
        if (src[i] === "/" && i + 1 < n && src[i + 1] === "-") {
          depth++;
          i += 2;
        } else if (src[i] === "-" && i + 1 < n && src[i + 1] === "/") {
          depth--;
          i += 2;
        } else {
          i++;
        }
      }
      out.push(fn(src.slice(start, i)));
      continue;
    }
    if (ch === "-" && nxt === "-") {
      const start = i;
      while (i < n && src[i] !== "\n") i++;
      out.push(fn(src.slice(start, i)));
      continue;
    }
    if (ch === '"') {
      const start = i;
      i++;
      while (i < n && src[i] !== '"') {
        if (src[i] === "\\" && i + 1 < n) {
          i += 2;
        } else {
          i++;
        }
      }
      if (i < n) i++;
      out.push(src.slice(start, i));
      continue;
    }
    out.push(ch);
    i++;
  }
  return out.join("");
}

const ANON_LICENSE_HEADER = [
  "/-",
  "Released under Apache 2.0 license.",
  "Anonymized supplementary artifact for double-blind peer review.",
  "-/",
].join("\n");

/** Strip identifying lines in leading copyright/author block comments, URLs, and internal wave/manuscript tags when `anonymize` is enabled. */
export function anonymizeLeanSource(
  sourceText: string,
  options?: AnonymizeLeanOptions
): string {
  let out = sourceText;
  let hasAnonLicenseHeader = false;
  // Replace leading `/- ... -/` header (excluding `/-! ... -/` module docstrings) if it mentions internal Copyright / Authors / SPDX;
  // preserve third-party open-source (`Vilin97/lean-pool`, `Math_XMUM`, `harfe`) attribution headers intact while marking the file as licensed.
  out = out.replace(/^\s*\/-(?!\!)[\s\S]*?-\/\s*\n?/, (hdr) => {
    if (/Adapted from\s+(?:Vilin97|harfe|leanprover)|Math_XMUM|\bharfe\b|MIT License/i.test(hdr)) {
      hasAnonLicenseHeader = true;
      return hdr;
    }
    if (/Copyright|Authors?:|SPDX-License-Identifier|Released under Apache/i.test(hdr)) {
      hasAnonLicenseHeader = true;
      return `${ANON_LICENSE_HEADER}\n`;
    }
    if (/Apache License/i.test(hdr)) {
      hasAnonLicenseHeader = true;
    }
    return hdr;
  });
  if (options?.ensureLicenseHeader && !hasAnonLicenseHeader) {
    // Drop any pre-import `-- ...` file-split banner lines at the very top of the file before prepending the license header
    out = out.replace(/^(?:[ \t]*--[^\n]*\n)+/, "");
    out = `${ANON_LICENSE_HEADER}\n${out.trimStart()}`;
  } else if (options?.ensureLicenseHeader) {
    // Also strip `-- Sub-module ... split out of ...` lines immediately after the license header before `import`
    out = out.replace(
      /^(\/-\nReleased under Apache 2\.0 license\.\nAnonymized supplementary artifact for double-blind peer review\.\n-\/\n)(?:[ \t]*--[^\n]*\n)+/,
      "$1"
    );
  }
  // Scrub any github.com/<owner>/<repo> user URLs in comments (preserving third-party open-source upstream repos)
  out = out.replace(
    /https?:\/\/github\.com\/(?!(?:leanprover|leanprover-community|argumentcomputer|ammkrn|Vilin97|harfe)\b)[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+/g,
    "https://anonymous.4open.science/r/anonymized-artifact"
  );
  // Apply comment-only typographic & internal-ticket scrubbing (leaving all Lean code tokens untouched)
  out = transformLeanCommentsOnly(out, (chunk) => scrubCommentChunkForAnonymity(chunk, options));
  return out;
}

/**
 * Replace or insert a concise, truthful top-level `/-! # <moduleName> ... -/` docstring for a shaken non-entry module
 * so pruned modules never advertise declarations or sections that were tree-shaken away.
 */
export function synthesizeSliceModuleDocstring(
  moduleName: string,
  keptDeclNames: readonly string[],
  sourceText: string
): string {
  const uniqueNames: string[] = [];
  const seen = new Set<string>();
  for (const nm of keptDeclNames) {
    if (!nm || nm === "(example)" || nm.startsWith("_")) continue;
    if (!seen.has(nm)) {
      seen.add(nm);
      uniqueNames.push(nm);
    }
  }
  let summaryLine: string;
  if (uniqueNames.length === 0) {
    summaryLine = "Standalone formalization slice providing shared notation and module exports.";
  } else if (uniqueNames.length <= 24) {
    summaryLine = `Standalone formalization slice retaining: ${uniqueNames.map((n) => `\`${n}\``).join(", ")}.`;
  } else {
    const head = uniqueNames.slice(0, 24).map((n) => `\`${n}\``).join(", ");
    summaryLine = `Standalone formalization slice retaining: ${head}, and ${uniqueNames.length - 24} further declarations.`;
  }
  const newDoc = `/-!\n# ${moduleName}\n\n${summaryLine}\n-/`;

  // Scan top-level lines to locate the first column-0 `/-! ... -/` module docstring (outside license header)
  const lines = sourceText.split("\n");
  let i = 0;
  let lastImportOrOptionLine = -1;
  let licenseEndLine = -1;
  while (i < lines.length) {
    const tr = lines[i].trimStart();
    if (tr.startsWith("/-") && !tr.startsWith("/-!") && !tr.startsWith("/--")) {
      let depth = 0;
      while (i < lines.length) {
        const ln = lines[i];
        for (let c = 0; c < ln.length - 1; c++) {
          if (ln[c] === "/" && ln[c + 1] === "-") {
            depth++;
            c++;
          } else if (ln[c] === "-" && ln[c + 1] === "/") {
            depth--;
            c++;
          }
        }
        if (depth <= 0) break;
        i++;
      }
      if (lastImportOrOptionLine < 0) {
        licenseEndLine = i;
      }
      i++;
      continue;
    }
    if (tr.startsWith("/-!")) {
      const docStart = i;
      let depth = 0;
      while (i < lines.length) {
        const ln = lines[i];
        for (let c = 0; c < ln.length - 1; c++) {
          if (ln[c] === "/" && ln[c + 1] === "-") {
            depth++;
            c++;
          } else if (ln[c] === "-" && ln[c + 1] === "/") {
            depth--;
            c++;
          }
        }
        i++;
        if (depth <= 0) break;
      }
      const origDocBody = lines
        .slice(docStart, i)
        .join("\n")
        .replace(/^\/-!\s*/, "")
        .replace(/\s*-\/$/, "")
        .trim();
      const preserveUpstreamNote = /^Adapted from\b/i.test(origDocBody)
        ? `/-!\n# ${moduleName}\n\n${origDocBody}\n\n${summaryLine}\n-/`
        : newDoc;
      const before = lines.slice(0, docStart);
      const after = lines.slice(i);
      return [...before, preserveUpstreamNote, ...after].join("\n").replace(/(?:[ \t]*\n){3,}/g, "\n\n");
    }
    if (/^\s*(?:import|set_option)\b/.test(lines[i])) {
      lastImportOrOptionLine = i;
      i++;
      continue;
    }
    if (
      tr === "" ||
      tr.startsWith("--") ||
      /^\s*(?:namespace|section|(?:scoped\s+)?open|universe|variable)\b/.test(lines[i])
    ) {
      i++;
      continue;
    }
    // Reached first substantive declaration without encountering any `/-! ... -/` module docstring
    break;
  }

  const insertAfter = lastImportOrOptionLine >= 0 ? lastImportOrOptionLine : licenseEndLine;
  if (insertAfter >= 0) {
    const before = lines.slice(0, insertAfter + 1);
    const after = lines.slice(insertAfter + 1);
    return [...before, "", newDoc, "", ...after].join("\n").replace(/(?:[ \t]*\n){3,}/g, "\n\n");
  }
  return `${newDoc}\n\n${sourceText}`.replace(/(?:[ \t]*\n){3,}/g, "\n\n");
}

const REFACTOR_TOMBSTONE_RE =
  /\b(?:W\d+-B\d+|W\d+-TAUT|TAUT-\d+|DELETE\s*\(|Removed\s+`?(?:theorem|lemma|def|structure|abbrev)|Previously\s+`?(?:theorem|lemma|def)|Historical\s+TODO|CLOSED\s+IN-TREE|deleted\s*(?:--|\u2014)\s*same\s+reasoning)\b/;

/** Return true if a comment-stripped snippet consists solely of context directives (`open`, `variable`, `set_option`, `omit`, `include`, `universe`) rather than substantive declarations. */
function isContextDirectiveOnlyCode(strippedCode: string): boolean {
  const lines = strippedCode.split("\n");
  let inMultilineDirective = false;
  for (const raw of lines) {
    const tr = raw.trim();
    if (!tr) {
      inMultilineDirective = false;
      continue;
    }
    if (/^(?:(?:scoped\s+)?open|set_option|universe)\b/.test(tr)) {
      inMultilineDirective = false;
      continue;
    }
    if (/^(?:variable|omit|include)\b/.test(tr) && !/\bin$/.test(tr)) {
      inMultilineDirective = true;
      continue;
    }
    if (inMultilineDirective && /^[ \t]+[\({\[A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9]/.test(raw) && !/\bin$/.test(tr)) {
      continue;
    }
    return false;
  }
  return true;
}

/**
 * Strip empty `namespace ... end` / `section ... end` shells, refactor-tombstone comments, and orphan `/-! ... -/`
 * section docstrings / `-- ====` banners left behind when all declarations in a section were pruned.
 * Preserves leading license headers, the primary module docstring, and (unless `dropSectionDocs` is set) docstrings preceding kept code.
 */
export function stripOrphanSectionHusks(
  sourceText: string,
  options?: { dropSectionDocs?: boolean }
): string {
  // Step 1: Iteratively remove empty `namespace X ... end X` and `section X ... end X` shells
  // whose interior contains zero substantive declarations after stripping comments/strings and context directives.
  let text = sourceText;
  for (let pass = 0; pass < 6; pass++) {
    const lines = text.split("\n");
    const openStack: Array<{ idx: number; kind: "namespace" | "section"; name: string }> = [];
    const dropRanges: Array<[number, number]> = [];
    for (let i = 0; i < lines.length; i++) {
      const tr = lines[i].trim();
      const mOpen = tr.match(/^(namespace|section)(?:\s+([A-Za-z0-9_.']+))?\s*(?:--.*)?$/);
      if (mOpen) {
        openStack.push({
          idx: i,
          kind: mOpen[1] as "namespace" | "section",
          name: mOpen[2] || "",
        });
        continue;
      }
      const mEnd = tr.match(/^end(?:\s+([A-Za-z0-9_.']+))?\s*(?:--.*)?$/);
      if (mEnd && openStack.length > 0) {
        const endName = mEnd[1] || "";
        const top = openStack[openStack.length - 1];
        if (top.name === endName) {
          openStack.pop();
          const inner = lines.slice(top.idx + 1, i).join("\n");
          const innerStripped = stripLeanCommentsAndStrings(inner);
          if (isContextDirectiveOnlyCode(innerStripped)) {
            dropRanges.push([top.idx, i]);
          }
        }
      }
    }
    if (dropRanges.length === 0) break;
    const dropped = new Uint8Array(lines.length);
    for (const [s, e] of dropRanges) {
      for (let k = s; k <= e; k++) dropped[k] = 1;
    }
    text = lines.filter((_, idx) => !dropped[idx]).join("\n");
  }

  // Step 2: Tokenize into top-level blocks (license header, module docstring, subsequent `/-! ... -/` blocks,
  // `-- ====` / `-- ----` / `-- §` banner blocks, standalone remark comments, context directives, blank lines, and code/decl-doc lines)
  // and drop non-primary section headers, tombstones, trailing orphan directives, or orphaned remarks not followed by live code.
  interface LineBlock {
    kind: "primaryDoc" | "sectionDoc" | "banner" | "remark" | "directive" | "blank" | "end" | "code";
    text: string;
  }
  const lines = text.split("\n");
  const blocks: LineBlock[] = [];
  let seenPrimaryModuleDoc = false;
  let i = 0;
  const isBannerLine = (tr: string): boolean =>
    /^--\s*(?:[=\-\u2500]{4,}|(?:\u00a7|Section\b|Part\b).*)/.test(tr);

  while (i < lines.length) {
    const tr = lines[i].trim();
    if (tr === "") {
      blocks.push({ kind: "blank", text: lines[i] });
      i++;
      continue;
    }
    if (tr.startsWith("/-") && !tr.startsWith("/--")) {
      const isModuleDoc = tr.startsWith("/-!");
      const isLeadingLicense = i === 0 && !isModuleDoc;
      const start = i;
      let depth = 0;
      while (i < lines.length) {
        const ln = lines[i];
        for (let c = 0; c < ln.length - 1; c++) {
          if (ln[c] === "/" && ln[c + 1] === "-") {
            depth++;
            c++;
          } else if (ln[c] === "-" && ln[c + 1] === "/") {
            depth--;
            c++;
          }
        }
        i++;
        if (depth <= 0) break;
      }
      const chunk = lines.slice(start, i).join("\n");
      if (isLeadingLicense) {
        blocks.push({ kind: "primaryDoc", text: chunk });
      } else if (isModuleDoc && !seenPrimaryModuleDoc) {
        seenPrimaryModuleDoc = true;
        blocks.push({ kind: "primaryDoc", text: chunk });
      } else if (isModuleDoc) {
        blocks.push({ kind: "sectionDoc", text: chunk });
      } else {
        blocks.push({ kind: "remark", text: chunk });
      }
      continue;
    }
    if (isBannerLine(tr)) {
      const start = i;
      i++;
      while (i < lines.length && lines[i].trim().startsWith("--")) {
        i++;
      }
      blocks.push({ kind: "banner", text: lines.slice(start, i).join("\n") });
      continue;
    }
    if (tr.startsWith("--")) {
      const start = i;
      i++;
      while (i < lines.length && lines[i].trim().startsWith("--") && !isBannerLine(lines[i].trim())) {
        i++;
      }
      blocks.push({ kind: "remark", text: lines.slice(start, i).join("\n") });
      continue;
    }
    if (/^end(?:\s+[A-Za-z0-9_.']+)?\s*(?:--.*)?$/.test(tr)) {
      blocks.push({ kind: "end", text: lines[i] });
      i++;
      continue;
    }
    // Group standalone `open` / `variable` / `universe` directives (including multi-line indented continuations, excluding `... in`)
    if (/^(?:(?:scoped\s+)?open|variable|universe)\b/.test(tr) && !/\bin\s*(?:--.*)?$/.test(tr)) {
      const start = i;
      const isVar = /^variable\b/.test(tr);
      i++;
      if (isVar) {
        while (
          i < lines.length &&
          /^[ \t]+[\({\[A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9]/.test(lines[i]) &&
          !/\bin\s*(?:--.*)?$/.test(lines[i].trim())
        ) {
          i++;
        }
      }
      blocks.push({ kind: "directive", text: lines.slice(start, i).join("\n") });
      continue;
    }
    blocks.push({ kind: "code", text: lines[i] });
    i++;
  }

  // Backward sweep: keep at most ONE immediately-preceding section header (`banner` + optional `sectionDoc`,
  // or standalone `sectionDoc`) right before each `code` block; drop tombstones, trailing directives, and orphaned remarks!
  const dropSectionDocs = options?.dropSectionDocs === true;
  const keepBlock = new Array<boolean>(blocks.length).fill(true);
  let hasCodeBelow = false;
  let consumedSectionDoc = false;
  let consumedBanner = false;
  for (let b = blocks.length - 1; b >= 0; b--) {
    const blk = blocks[b];
    if (blk.kind === "blank" || blk.kind === "primaryDoc") {
      continue;
    }
    if (blk.kind === "end") {
      hasCodeBelow = false;
      consumedSectionDoc = false;
      consumedBanner = false;
      continue;
    }
    if (blk.kind === "directive") {
      if (!hasCodeBelow) {
        keepBlock[b] = false;
      }
      continue;
    }
    if (blk.kind === "code") {
      const stripped = stripLeanCommentsAndStrings(blk.text).trim();
      if (
        stripped !== "" &&
        !/^(?:set_option|import|namespace|section)\b/.test(stripped)
      ) {
        hasCodeBelow = true;
        consumedSectionDoc = false;
        consumedBanner = false;
      }
      continue;
    }
    if (blk.kind === "remark") {
      if (REFACTOR_TOMBSTONE_RE.test(blk.text) || !hasCodeBelow || consumedBanner || consumedSectionDoc) {
        keepBlock[b] = false;
      }
      continue;
    }
    if (blk.kind === "sectionDoc") {
      if (dropSectionDocs || !hasCodeBelow || consumedSectionDoc || consumedBanner) {
        keepBlock[b] = false;
      } else {
        consumedSectionDoc = true;
      }
      continue;
    }
    if (blk.kind === "banner") {
      if (dropSectionDocs || !hasCodeBelow || consumedBanner) {
        keepBlock[b] = false;
      } else {
        consumedBanner = true;
      }
      continue;
    }
  }

  const keptText = blocks
    .filter((_, idx) => keepBlock[idx])
    .map((blk) => blk.text)
    .join("\n");
  return keptText.replace(/(?:[ \t]*\n){3,}/g, "\n\n");
}

/** Strip nested `/- ... -/` comments, `-- ...` line comments, and `"..."` strings while preserving newlines. */
export { stripLeanCommentsAndStrings } from "./lean_source.ts";

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
    const keptSet = allKeptModules ?? new Set<string>([...keptProjectImports, ...promotedProjectImports]);
    for (let len = parts.length; len >= 1; len--) {
      const pref = parts.slice(0, len).join(".");
      if (isProjectModule(pref)) {
        if (keptSet.has(pref)) return false;
        for (const km of keptSet) {
          if (km.startsWith(pref + ".")) return false;
        }
        return true;
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

  const normalizeExternalImport = (imp: string): string =>
    imp === "Mathlib.Data.Real.Basic" ? "Mathlib.Basic.Real.Basic" : imp;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const m = line.match(/^\s*import\s+([A-Za-z0-9_.']+)\s*(?:--.*)?$/);
    if (m) {
      const rawImp = m[1];
      if (isProjectModule(rawImp) && !keptProjectImports.has(rawImp)) {
        continue;
      }
      const impMod = isProjectModule(rawImp) ? rawImp : normalizeExternalImport(rawImp);
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
  canKeepGlobalAttr?: (sp: ParsedDeclSpan) => boolean,
  activeSyntaxKeywords?: ReadonlySet<string>
): { prunedText: string; keptCount: number; prunedCount: number; keptDeclNames: string[] } {
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
    const baseTxt = activeSyntaxKeywords
      ? stripOrphanSectionHusks(stripUnusedSyntaxBlocks(sourceText, activeSyntaxKeywords)).replace(/\n{3,}/g, "\n\n")
      : sourceText;
    return { prunedText: baseTxt, keptCount: 0, prunedCount: 0, keptDeclNames: [] };
  }

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

  // Same-module value/type definitions: an `instance` or `@[simp]`/`@[ext]` lemma should only
  // auto-retain if every same-module definition/type in its signature head (`headText`) is already kept.
  const localCarrierNames = new Set<string>();
  for (const sp of spans) {
    if (
      sp.bareName &&
      (sp.kind === "def" ||
        sp.kind === "abbrev" ||
        sp.kind === "structure" ||
        sp.kind === "class" ||
        sp.kind === "inductive")
    ) {
      localCarrierNames.add(sp.bareName);
    }
  }

  const headCarriersSatisfied = (sp: ParsedDeclSpan, keptCarrierSet: ReadonlySet<string>): boolean => {
    const headTokens = extractIdentifierSet(sp.headText);
    for (const tok of headTokens) {
      if (tok === sp.bareName) continue;
      if (localCarrierNames.has(tok) && !keptCarrierSet.has(tok)) {
        return false;
      }
    }
    return true;
  };

  const isDirectlyReachable = (sp: ParsedDeclSpan): boolean => {
    if (sp.kind === "example" || sp.isDeprecated) return false;
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

  const keptFlags = spans.map(isDirectlyReachable);

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
    const keptCarrierSet = new Set<string>();
    for (let i = 0; i < spans.length; i++) {
      if (keptFlags[i] && localCarrierNames.has(spans[i].bareName)) {
        keptCarrierSet.add(spans[i].bareName);
      }
    }
    for (let i = 0; i < spans.length; i++) {
      if (keptFlags[i]) continue;
      const sp = spans[i];
      if (
        sp.hasGlobalAttr &&
        (!canKeepGlobalAttr || canKeepGlobalAttr(sp)) &&
        headCarriersSatisfied(sp, keptCarrierSet)
      ) {
        keptFlags[i] = true;
        changed = true;
      }
    }
    const corpusForScan = activeSyntaxKeywords
      ? stripUnusedSyntaxBlocks(buildKeptCorpus(), activeSyntaxKeywords)
      : buildKeptCorpus();
    const codeOnly = stripStructuralHeaderLines(
      stripLeanCommentsAndStrings(stripSmokeCommands(corpusForScan))
    );
    const activeTokens = extractIdentifierSet(codeOnly);
    for (let i = 0; i < spans.length; i++) {
      if (keptFlags[i]) continue;
      const sp = spans[i];
      if (sp.kind === "example" || sp.isDeprecated) continue;
      if (sp.bareName && activeTokens.has(sp.bareName)) {
        keptFlags[i] = true;
        changed = true;
      }
    }
  }

  let keptCount = 0;
  let prunedCount = 0;
  const keptDeclNames: string[] = [];
  const rawPrunedNames: string[] = [];
  const outChunks: Buffer[] = [];
  let cursor = 0;
  for (let i = 0; i < spans.length; i++) {
    const sp = spans[i];
    if (sp.startByte > cursor) {
      outChunks.push(buf.subarray(cursor, sp.startByte));
    }
    if (keptFlags[i]) {
      keptCount++;
      if (sp.bareName && sp.kind !== "example") {
        keptDeclNames.push(sp.bareName);
      }
      outChunks.push(buf.subarray(sp.startByte, sp.endByte));
    } else {
      prunedCount++;
      if (sp.bareName && sp.kind !== "example") {
        rawPrunedNames.push(sp.bareName);
      }
      if (sp.name && sp.name !== sp.bareName && sp.kind !== "example") {
        rawPrunedNames.push(sp.name);
      }
    }
    cursor = sp.endByte;
  }
  if (cursor < buf.length) {
    outChunks.push(buf.subarray(cursor));
  }

  const keptNameSet = new Set(keptDeclNames);
  const prunedOnlyNames = Array.from(new Set(rawPrunedNames)).filter((nm) => nm && !keptNameSet.has(nm));

  let assembled = Buffer.concat(outChunks).toString("utf-8");
  if (prunedOnlyNames.length > 0 && prunedOnlyNames.length <= 2000) {
    const escapedAlts = prunedOnlyNames
      .map((nm) => nm.replace(/[.*+?^${}()|[\]\\]/g, "\\$&"))
      .join("|");
    const parenSeeRe = new RegExp(`\\s*\\(\\s*see\\s+\`(?:[A-Za-z0-9_']+\\.)?(?:${escapedAlts})\`[^()]*\\)`, "gi");
    const semiSeeRe = new RegExp(`;\\s*see\\s+\`(?:[A-Za-z0-9_']+\\.)?(?:${escapedAlts})\`[^.;)\\n]*`, "gi");
    assembled = transformLeanCommentsOnly(assembled, (chunk) => {
      if (!chunk.startsWith("/--")) return chunk;
      return chunk.replace(parenSeeRe, "").replace(semiSeeRe, "");
    });
  }
  if (activeSyntaxKeywords) {
    assembled = stripUnusedSyntaxBlocks(assembled, activeSyntaxKeywords);
  }
  let prunedText = stripOrphanSectionHusks(stripSmokeCommands(assembled));
  // Collapse 3+ consecutive blank lines left behind by pruned spans into 2 newlines
  prunedText = prunedText.replace(/\n{3,}/g, "\n\n");
  return { prunedText, keptCount, prunedCount, keptDeclNames };
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

/** Generate a minimal, clean Lake configuration matching `lean-manifest.json` dependencies (pruning unused non-inherited external git packages). */
function buildStandaloneLakefile(
  leanRoot: string,
  packageName: string,
  topPrefixes: readonly string[],
  anonymize: boolean,
  usedExternalRootsLower?: ReadonlySet<string>
): { filename: string; content: string } {
  const origLakefileLean = path.join(leanRoot, "lakefile.lean");
  const origLakefileToml = path.join(leanRoot, "lakefile.toml");

  if (!anonymize && fs.existsSync(origLakefileToml)) {
    return { filename: "lakefile.toml", content: fs.readFileSync(origLakefileToml, "utf-8") };
  }

  const isExternalGitRequireUsed = (reqPkgName: string): boolean => {
    if (!usedExternalRootsLower || usedExternalRootsLower.size === 0) return true;
    const low = reqPkgName.toLowerCase();
    if (low === "mathlib") return usedExternalRootsLower.has("mathlib") || usedExternalRootsLower.has("aesop") || usedExternalRootsLower.has("batteries") || usedExternalRootsLower.has("qq");
    return usedExternalRootsLower.has(low);
  };

  // Extract `require ...` blocks from `lakefile.lean` if present so package pins match `lake-manifest.json`
  let requireBlocks: string[] = [];
  if (fs.existsSync(origLakefileLean)) {
    const raw = fs.readFileSync(origLakefileLean, "utf-8");
    const reqRe = /^\s*require\s+([A-Za-z0-9_]+)\s+from\s+git\s*\n?\s*"[^"]+"\s*@\s*"[^"]+"/gm;
    let m: RegExpExecArray | null;
    while ((m = reqRe.exec(raw)) !== null) {
      if (isExternalGitRequireUsed(m[1])) {
        requireBlocks.push(m[0].trim());
      }
    }
  }
  if (requireBlocks.length === 0) {
    const manifestPath = path.join(leanRoot, "lake-manifest.json");
    if (fs.existsSync(manifestPath)) {
      try {
        const mf = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
        for (const pkg of mf.packages || []) {
          if (
            pkg &&
            pkg.inherited === false &&
            pkg.type !== "path" &&
            pkg.name &&
            pkg.url &&
            (pkg.inputRev || pkg.rev) &&
            isExternalGitRequireUsed(String(pkg.name))
          ) {
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

  const localPkgDirs = discoverLocalPathPackageDirs(leanRoot);
  const searchRoots = [leanRoot, ...localPkgDirs];
  const ileanPaths = collectProjectIleanFiles(leanRoot, localPkgDirs);
  if (ileanPaths.length === 0) {
    throw new Error(
      `No compiled .ilean files found under ${leanRoot}/.lake/build/lib; run 'lake build ${entryModules.join(" ")}' first`
    );
  }

  const moduleSourceRel = new Map<string, string>();
  const moduleSourceAbs = new Map<string, string>();
  const moduleDirectImports = new Map<string, string[]>();
  const moduleDecls = new Map<string, Set<string>>();
  // callerQualId -> Array<{ targetModule, targetId, rawName }>
  const declEdges = new Map<string, Array<{ targetModule: string; targetId: string; rawName: string }>>();
  // module -> set of referenced target modules (across all usages in the file, or per decl)
  const moduleTopRefs = new Map<string, Array<{ targetModule: string; targetId: string; rawName: string }>>();
  const declRefModules = new Map<string, Set<string>>();

  // Pass 1: load all project `.ilean` files whose `.lean` source exists under `leanRoot` or `localPkgDirs`
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
    if (!mod || moduleSourceRel.has(mod)) continue;
    const relLean = mod.replace(/\./g, "/") + ".lean";
    let absLean = "";
    for (const sr of searchRoots) {
      const cand = path.join(sr, relLean);
      if (fs.existsSync(cand)) {
        absLean = cand;
        break;
      }
    }
    if (!absLean) continue;

    moduleSourceRel.set(mod, relLean);
    moduleSourceAbs.set(mod, absLean);
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
      if (isProjectModule(imp)) {
        if (!fileClosure.has(imp)) {
          modQueue.push(imp);
        }
      } else {
        const relImp = imp.replace(/\./g, "/") + ".lean";
        if (searchRoots.some((sr) => fs.existsSync(path.join(sr, relImp)))) {
          throw new Error(
            `Project module '${imp}' (imported by '${curr}') exists on disk (${relImp}) without a compiled .ilean; run 'lake build ${entryModules.join(" ")}' first`
          );
        }
      }
    }
  }

  // Precompute transitive project imports inside `fileClosure` for each module
  const transProjImports = new Map<string, Set<string>>();
  for (const mod of fileClosure) {
    const seen = new Set<string>();
    const q = [...(moduleDirectImports.get(mod) || [])];
    while (q.length > 0) {
      const nxt = q.shift()!;
      if (!fileClosure.has(nxt) || seen.has(nxt)) continue;
      seen.add(nxt);
      for (const sub of moduleDirectImports.get(nxt) || []) {
        if (fileClosure.has(sub) && !seen.has(sub)) q.push(sub);
      }
    }
    transProjImports.set(mod, seen);
  }

  // Detect notation-provider vs tactic/macro/elab-provider modules inside `fileClosure`
  const notationModules = new Set<string>();
  const tacticSyntaxModules = new Set<string>();
  const syntaxAnalysisByModule = new Map<string, ModuleSyntaxAnalysis>();
  const activeKeywordsByModule = new Map<string, Set<string>>();
  const moduleRawSourceCache = new Map<string, string>();
  const getModuleRawSource = (mod: string): string => {
    let txt = moduleRawSourceCache.get(mod);
    if (txt !== undefined) return txt;
    const abs = moduleSourceAbs.get(mod);
    txt = abs && fs.existsSync(abs) ? fs.readFileSync(abs, "utf-8") : "";
    moduleRawSourceCache.set(mod, txt);
    return txt;
  };

  for (const mod of fileClosure) {
    try {
      const txt = getModuleRawSource(mod);
      const codeNoComments = stripLeanCommentsAndStrings(txt);
      if (NOTATION_PROVIDER_RE.test(codeNoComments)) {
        notationModules.add(mod);
      }
      if (TACTIC_SYNTAX_PROVIDER_RE.test(codeNoComments)) {
        const analysis = analyzeModuleSyntax(txt);
        if (analysis.allKeywords.size > 0) {
          tacticSyntaxModules.add(mod);
          syntaxAnalysisByModule.set(mod, analysis);
          activeKeywordsByModule.set(mod, new Set<string>());
        }
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
      // Keep any notation-providing module directly imported by `mod`
      for (const imp of moduleDirectImports.get(mod) || []) {
        if (notationModules.has(imp)) {
          usedModulesByModule.get(mod)!.add(imp);
          markNotationModuleClosure(imp);
        }
      }
    }
  };

  const markNotationModuleClosure = (notMod: string) => {
    if (keptModules.has(notMod)) return;
    markModuleKept(notMod);
    for (const d of moduleDecls.get(notMod) || []) {
      enqueueTarget(notMod, normalizeQualifiedDeclId(notMod, d), d);
    }
    for (const top of moduleTopRefs.get(notMod) || []) {
      usedModulesByModule.get(notMod)!.add(top.targetModule);
      enqueueTarget(top.targetModule, top.targetId, top.rawName);
    }
    for (const imp of moduleDirectImports.get(notMod) || []) {
      if (notationModules.has(imp)) {
        usedModulesByModule.get(notMod)!.add(imp);
        markNotationModuleClosure(imp);
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

  const drainDeclQueue = () => {
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
      // Retain module-level anonymous/instance/command references of `mod` once `mod` is kept,
      // EXCEPT in `tacticSyntaxModules` (where top-level unattributed commands may be self-smoke macro calls!).
      if (!entryModules.includes(mod) && !tacticSyntaxModules.has(mod)) {
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

  drainDeclQueue();

  // Ensure every kept module retains outgoing cross-module references of `instance` declarations
  // whose same-module signature-head carriers are already reachable (avoiding dead `QTraj.inst*`-style bloat).
  const moduleInstanceSpansCache = new Map<string, ParsedDeclSpan[]>();
  const getModuleFallbackSpans = (mod: string): ParsedDeclSpan[] => {
    let cached = moduleInstanceSpansCache.get(mod);
    if (cached) return cached;
    const ilean = parsedIleans.get(mod);
    const raw = getModuleRawSource(mod);
    if (!raw || !ilean?.decls) {
      cached = [];
    } else {
      try {
        cached = parseIleanFallbackSpans(raw, Buffer.from(raw, "utf-8"), ilean.decls);
      } catch {
        cached = [];
      }
    }
    moduleInstanceSpansCache.set(mod, cached);
    return cached;
  };

  const drainInstancesAndQueue = (): boolean => {
    let anyChanged = false;
    let instChanged = true;
    while (instChanged) {
      instChanged = false;
      for (const mod of Array.from(keptModules)) {
        const spansForMod = getModuleFallbackSpans(mod);
        const localCarriers = new Set<string>();
        for (const sp of spansForMod) {
          if (
            sp.bareName &&
            (sp.kind === "def" ||
              sp.kind === "abbrev" ||
              sp.kind === "structure" ||
              sp.kind === "class" ||
              sp.kind === "inductive")
          ) {
            localCarriers.add(sp.bareName);
          }
        }
        const modReach = reachableByModule.get(mod) || new Set<string>();
        for (const sp of spansForMod) {
          if (sp.kind !== "instance" || sp.isDeprecated) continue;
          const qid = normalizeQualifiedDeclId(mod, sp.name);
          if (visitedDeclKeys.has(`${mod}::${qid}`)) continue;
          const headIdents =
            sp.headText.match(/[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2080-\u2089]*/g) || [];
          let headOk = true;
          for (const tok of headIdents) {
            if (tok === sp.bareName) continue;
            if (localCarriers.has(tok) && !modReach.has(tok)) {
              headOk = false;
              break;
            }
          }
          if (!headOk) continue;
          enqueueTarget(mod, qid, sp.name);
          instChanged = true;
          anyChanged = true;
        }
        if (declQueue.length > 0) {
          drainDeclQueue();
          anyChanged = true;
        }
      }
    }
    return anyChanged;
  };

  drainInstancesAndQueue();

  // Joint fixed-point over surface-syntax-token tactic/macro activation + `.ilean` / `instance` reachability:
  // Only tactics/macros whose surface keyword actually appears in active caller code are retained!
  if (tacticSyntaxModules.size > 0) {
    const getActiveCallerCodeForSyntaxScan = (callerMod: string): string => {
      const raw = getModuleRawSource(callerMod);
      if (!raw) return "";
      if (entryModules.includes(callerMod)) {
        return stripLeanCommentsAndStrings(raw);
      }
      const modReach = reachableByModule.get(callerMod) || new Set<string>();
      const spans = getModuleFallbackSpans(callerMod);
      const isSpanActive = (sp: ParsedDeclSpan): boolean => {
        if (sp.kind === "example" || sp.isDeprecated) return false;
        const qid = normalizeQualifiedDeclId(callerMod, sp.name);
        if (modReach.has(qid) || modReach.has(sp.name) || modReach.has(sp.bareName)) return true;
        if (sp.hasGlobalAttr) {
          // Conservatively include global-attr spans whose local carriers are reachable
          const localCarriers = new Set<string>();
          for (const s2 of spans) {
            if (
              s2.bareName &&
              (s2.kind === "def" ||
                s2.kind === "abbrev" ||
                s2.kind === "structure" ||
                s2.kind === "class" ||
                s2.kind === "inductive")
            ) {
              localCarriers.add(s2.bareName);
            }
          }
          const hIds =
            sp.headText.match(/[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2080-\u2089]*/g) || [];
          return hIds.every((tok) => tok === sp.bareName || !localCarriers.has(tok) || modReach.has(tok));
        }
        return false;
      };

      if (tacticSyntaxModules.has(callerMod)) {
        const parts: string[] = [];
        const rawBuf = Buffer.from(raw, "utf-8");
        for (const sp of spans) {
          if (isSpanActive(sp)) {
            parts.push(rawBuf.subarray(sp.startByte, sp.endByte).toString("utf-8"));
          }
        }
        const synAn = syntaxAnalysisByModule.get(callerMod);
        const actKws = activeKeywordsByModule.get(callerMod);
        if (synAn && actKws && actKws.size > 0) {
          for (const blk of synAn.blocks) {
            if (blk.keywords.some((kw) => actKws.has(kw)) && blk.bodyText) {
              parts.push(blk.bodyText);
            }
          }
        }
        return stripLeanCommentsAndStrings(parts.join("\n"));
      }

      // Non-syntax kept module: mask out inactive declaration spans so dead proofs do not pull in tactics,
      // while preserving kept spans and any top-level command macro invocations.
      if (spans.length === 0) {
        return stripLeanCommentsAndStrings(
          raw
            .split("\n")
            .filter((ln) => !/^\s*#(?:check|eval|print|reduce)\b/.test(ln))
            .join("\n")
        );
      }
      const rawBuf = Buffer.from(raw, "utf-8");
      const keptChunks: Buffer[] = [];
      let cursor = 0;
      for (const sp of spans) {
        if (sp.startByte > cursor) {
          keptChunks.push(rawBuf.subarray(cursor, sp.startByte));
        }
        if (isSpanActive(sp)) {
          keptChunks.push(rawBuf.subarray(sp.startByte, sp.endByte));
        } else {
          keptChunks.push(Buffer.from("\n", "utf-8"));
        }
        cursor = sp.endByte;
      }
      if (cursor < rawBuf.length) {
        keptChunks.push(rawBuf.subarray(cursor));
      }
      const masked = Buffer.concat(keptChunks)
        .toString("utf-8")
        .split("\n")
        .filter((ln) => !/^\s*#(?:check|eval|print|reduce)\b/.test(ln))
        .join("\n");
      return stripLeanCommentsAndStrings(masked);
    };

    const enqueueSyntaxBlockDependencies = (synMod: string, blk: ModuleSyntaxBlock) => {
      const synAn = syntaxAnalysisByModule.get(synMod);
      if (synAn && blk.synIdent) {
        for (const fnName of synAn.tacticAttrEvaluators.get(blk.synIdent) || []) {
          enqueueTarget(synMod, normalizeQualifiedDeclId(synMod, fnName), fnName);
        }
      }
      if (!blk.bodyText) return;
      const bodyClean = stripLeanCommentsAndStrings(blk.bodyText);
      const idTokens = new Set<string>(
        bodyClean.match(/[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2080-\u2089]*/g) || []
      );
      if (idTokens.size === 0) return;
      const candidateTargetMods = [
        synMod,
        ...(moduleDirectImports.get(synMod) || []).filter((m) => fileClosure.has(m)),
      ];
      for (const tMod of candidateTargetMods) {
        const parsed = parsedIleans.get(tMod);
        if (!parsed?.decls) continue;
        for (const dName of Object.keys(parsed.decls)) {
          if (dName.startsWith("_private.")) continue;
          const shortName = dName.split(".").pop() || dName;
          if (idTokens.has(shortName) || idTokens.has(dName)) {
            if (tMod !== synMod) {
              usedModulesByModule.get(synMod)!.add(tMod);
            }
            enqueueTarget(tMod, normalizeQualifiedDeclId(tMod, dName), dName);
          }
        }
      }
    };

    let syntaxLoopChanged = true;
    while (syntaxLoopChanged) {
      syntaxLoopChanged = false;
      for (const callerMod of Array.from(keptModules)) {
        const transImps = transProjImports.get(callerMod) || new Set<string>();
        const candidateSynMods: string[] = [];
        if (tacticSyntaxModules.has(callerMod)) candidateSynMods.push(callerMod);
        for (const sm of tacticSyntaxModules) {
          if (sm !== callerMod && transImps.has(sm)) candidateSynMods.push(sm);
        }
        if (candidateSynMods.length === 0) continue;

        const callerCode = getActiveCallerCodeForSyntaxScan(callerMod);
        if (!callerCode) continue;

        for (const synMod of candidateSynMods) {
          const synAn = syntaxAnalysisByModule.get(synMod)!;
          const activeSet = activeKeywordsByModule.get(synMod)!;
          let callerUsesSynMod = false;
          for (const blk of synAn.blocks) {
            if (blk.keywords.length === 0) continue;
            const matched = blk.keywords.some((kw) => codeContainsSurfaceKeyword(callerCode, kw));
            if (matched) {
              callerUsesSynMod = true;
              let newlyActivatedBlock = false;
              for (const kw of blk.keywords) {
                if (!activeSet.has(kw)) {
                  activeSet.add(kw);
                  newlyActivatedBlock = true;
                  syntaxLoopChanged = true;
                }
              }
              if (newlyActivatedBlock) {
                markModuleKept(synMod);
                enqueueSyntaxBlockDependencies(synMod, blk);
              }
            }
          }
          if (callerUsesSynMod) {
            if (!keptModules.has(synMod)) {
              markModuleKept(synMod);
              syntaxLoopChanged = true;
            }
            if (synMod !== callerMod && !usedModulesByModule.get(callerMod)!.has(synMod)) {
              usedModulesByModule.get(callerMod)!.add(synMod);
              syntaxLoopChanged = true;
            }
          }
        }
      }
      if (declQueue.length > 0) {
        drainDeclQueue();
        syntaxLoopChanged = true;
      }
      if (drainInstancesAndQueue()) {
        syntaxLoopChanged = true;
      }
    }
  }

  // Corpus baseline metrics
  const corpusStats = countCorpusLeanFiles(leanRoot, topPrefixes, localPkgDirs);

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

  // Helper: collect external (`!isProjectModule`, non-`Init`, non-umbrella `Mathlib`) imports transitively provided by a set of project modules
  const collectTransitiveExternalImports = (seedMods: Iterable<string>): Set<string> => {
    const ext = new Set<string>();
    const seenProj = new Set<string>();
    const q = Array.from(seedMods);
    while (q.length > 0) {
      const m = q.shift()!;
      if (seenProj.has(m)) continue;
      seenProj.add(m);
      for (const rawImp of moduleDirectImports.get(m) || []) {
        if (isProjectModule(rawImp)) {
          if (!seenProj.has(rawImp)) q.push(rawImp);
        } else if (rawImp && rawImp !== "Init" && !rawImp.startsWith("Init.") && rawImp !== "Mathlib") {
          const normImp = rawImp === "Mathlib.Data.Real.Basic" ? "Mathlib.Basic.Real.Basic" : rawImp;
          ext.add(normImp);
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

  const keptModuleNamesSet = new Set<string>(sortedKeptModules);
  const keptModuleBaseNamesSet = new Set<string>();
  for (const mod of sortedKeptModules) {
    const rel = moduleSourceRel.get(mod);
    if (rel) {
      const base = rel.split("/").pop();
      if (base) keptModuleBaseNamesSet.add(base);
    }
  }
  const anonOptions: AnonymizeLeanOptions = {
    ensureLicenseHeader: true,
    keptModuleNames: keptModuleNamesSet,
    keptModuleBaseNames: keptModuleBaseNamesSet,
  };

  for (const mod of sortedKeptModules) {
    const relPath = moduleSourceRel.get(mod)!;
    const absPath = moduleSourceAbs.get(mod)!;
    const rawSource = getModuleRawSource(mod);
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
    let fullFallback = anonymize ? anonymizeLeanSource(rawSource, anonOptions) : rawSource;
    fullFallback = rewriteModuleImports(
      fullFallback,
      isProjectModule,
      baseKeptImps,
      allPromoted,
      modAvailableModules,
      isNamespaceUnavailable,
      isIdentUnavailableInVariable
    );
    if (anonymize && !entryModules.includes(mod)) {
      const fallbackSpans = getModuleFallbackSpans(mod);
      const fallbackNames = fallbackSpans
        .filter((s) => s.kind !== "example" && !s.isDeprecated && Boolean(s.bareName))
        .map((s) => s.bareName);
      fullFallback = synthesizeSliceModuleDocstring(mod, fallbackNames, fullFallback);
    }
    moduleFullFallbackOutputs.set(mod, fullFallback);

    // IMPORTANT: Prune declaration byte spans on `rawSource` FIRST so `@startByte:endByte` align
    // byte-for-byte with `rawSource`, THEN anonymize & rewrite imports!
    let finalText = fullFallback;
    let keptDeclCount = Math.max(1, Math.floor((moduleDecls.get(mod)?.size ?? 2) / 2));
    let prunedDeclCount = 0;

    if (granularity === "declaration" && !entryModules.includes(mod) && !notationModules.has(mod)) {
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
      const activeSynKws = tacticSyntaxModules.has(mod)
        ? activeKeywordsByModule.get(mod) ?? new Set<string>()
        : undefined;
      const pruned = pruneModuleDeclarations(
        absPath,
        rawSource,
        bareSet,
        reachSet,
        options.analyzerBin,
        parsedIleans.get(mod)?.decls,
        canKeepAttr,
        activeSynKws
      );
      let rewrittenPruned = anonymize
        ? anonymizeLeanSource(pruned.prunedText, anonOptions)
        : pruned.prunedText;
      rewrittenPruned = rewriteModuleImports(
        rewrittenPruned,
        isProjectModule,
        baseKeptImps,
        allPromoted,
        modAvailableModules,
        isNamespaceUnavailable,
        isIdentUnavailableInVariable
      );
      if (anonymize) {
        rewrittenPruned = synthesizeSliceModuleDocstring(mod, pruned.keptDeclNames, rewrittenPruned);
      }
      finalText = stripOrphanSectionHusks(rewrittenPruned, {
        dropSectionDocs: anonymize,
      });
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

  // Collect actually imported external root package prefixes across all emitted slice modules
  const usedExternalRootsLower = new Set<string>();
  for (const content of moduleOutputs.values()) {
    const impMatches = content.matchAll(/^\s*import\s+([A-Za-z0-9_']+)/gm);
    for (const im of impMatches) {
      const rootSeg = im[1];
      if (!topPrefixes.has(rootSeg) && rootSeg !== "Init") {
        usedExternalRootsLower.add(rootSeg.toLowerCase());
      }
    }
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
    // Clean any stale `.lean` files from a prior tree-shake run into the same `outputDir` (preserving `.lake` if present)
    for (const pref of ["AltProof", ...Array.from(topPrefixes)]) {
      const staleDir = path.join(resolvedOutDir, pref);
      if (fs.existsSync(staleDir)) {
        fs.rmSync(staleDir, { recursive: true, force: true });
      }
      const staleTop = path.join(resolvedOutDir, `${pref}.lean`);
      if (fs.existsSync(staleTop)) {
        fs.rmSync(staleTop, { force: true });
      }
    }

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
      const mathlibUsed =
        usedExternalRootsLower.has("mathlib") ||
        usedExternalRootsLower.has("aesop") ||
        usedExternalRootsLower.has("batteries") ||
        usedExternalRootsLower.has("qq");
      if (Array.isArray(mfJson.packages)) {
        mfJson.packages = mfJson.packages.filter(
          (pkg: { type?: string; name?: string; inherited?: boolean } | null) => {
            if (!pkg || !pkg.name) return false;
            if (pkg.type === "path" && !EXTERNAL_OR_CACHE_PACKAGE_NAMES.has(pkg.name)) {
              return false;
            }
            // Drop unused direct (`inherited === false`) external git dependencies such as `LSpec`
            if (pkg.inherited === false && pkg.type === "git" && usedExternalRootsLower.size > 0) {
              const low = pkg.name.toLowerCase();
              if (low === "mathlib") return mathlibUsed;
              return usedExternalRootsLower.has(low);
            }
            return true;
          }
        );
      }
      fs.writeFileSync(path.join(resolvedOutDir, "lake-manifest.json"), JSON.stringify(mfJson, null, 2) + "\n", "utf-8");
    }
    const lf = buildStandaloneLakefile(leanRoot, pkgName, keptTopPrefixes, anonymize, usedExternalRootsLower);
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

    const licenseLines = [
      "Apache License",
      "Version 2.0, January 2004",
      "http://www.apache.org/licenses/",
      "",
      "Unless otherwise noted in an individual file header, this supplementary Lean 4",
      "formalization artifact is licensed under the Apache License, Version 2.0.",
      "You may obtain a copy of the License at:",
      "",
      "    http://www.apache.org/licenses/LICENSE-2.0",
      "",
      "Unless required by applicable law or agreed to in writing, software",
      'distributed under the License is distributed on an "AS IS" BASIS,',
      "WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.",
      "See the License for the specific language governing permissions and",
      "limitations under the License.",
      "",
      "------------------------------------------------------------------------",
      "Third-Party Permissive Notices (retained in respective module headers):",
      "",
      "1. Scarf / Brouwer / Mixed Nash fixed-point modules",
      "   Adapted from Vilin97/lean-pool (https://github.com/Vilin97/lean-pool),",
      "   Copyright (c) 2026 Math_XMUM, licensed under the Apache License, Version 2.0.",
      "",
      "2. Cubical-Sperner Brouwer & Kakutani fixed-point modules",
      "   Adapted from harfe/fixed-point-theorems-lean4",
      "   (https://github.com/harfe/fixed-point-theorems-lean4),",
      "   Copyright (c) harfe / fixed-point-theorems-lean4 contributors,",
      "   licensed under the MIT License:",
      "   Permission is hereby granted, free of charge, to any person obtaining a copy",
      '   of this software and associated documentation files (the "Software"), to deal',
      "   in the Software without restriction, including without limitation the rights",
      "   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell",
      "   copies of the Software, and to permit persons to whom the Software is",
      "   furnished to do so, subject to the above copyright notice and this permission",
      "   notice being included in all copies or substantial portions of the Software.",
      "",
    ];
    fs.writeFileSync(path.join(resolvedOutDir, "LICENSE"), licenseLines.join("\n"), "utf-8");

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
      // Exclude `.lake` defensively, strip all UID/GID/mtime host metadata, and compress in-process
      // via `node:zlib` (`mtime: 0`) so restricted sandboxes never need to fork `/bin/gzip`.
      let tarStdout: Buffer | null = null;
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
          "-cf",
          "-",
          "-C",
          resolvedOutDir,
          ".",
        ],
        { maxBuffer: 256 * 1024 * 1024 }
      );
      if (tarRes.status === 0 && Buffer.isBuffer(tarRes.stdout)) {
        tarStdout = tarRes.stdout;
      } else {
        // Portable BSD/macOS tar fallback if GNU `--sort=name` / `--mtime` is unsupported
        const fallbackTar = spawnSync(
          "tar",
          ["--exclude=.lake", "--exclude=.git", "-cf", "-", "-C", resolvedOutDir, "."],
          { maxBuffer: 256 * 1024 * 1024 }
        );
        if (fallbackTar.status !== 0 || !Buffer.isBuffer(fallbackTar.stdout)) {
          const errMsg = (fallbackTar.stderr || tarRes.stderr || Buffer.alloc(0)).toString("utf-8");
          throw new Error(`Failed to create archive ${absArchive}: ${errMsg}`);
        }
        tarStdout = fallbackTar.stdout;
      }
      const gzBytes = absArchive.endsWith(".tar")
        ? tarStdout
        : zlib.gzipSync(tarStdout, { level: 9 });
      fs.writeFileSync(absArchive, gzBytes);
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
