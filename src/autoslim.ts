import { readRankingHistory, rankTactics, candidatePriority } from "./autoslim_ranking.ts";
// src/autoslim.ts
// Kernel-verified proof auto-slimmer wiring lean-analyzer ALTPROOF-ROUTE quickfix spans
// to real Lean 4 elaboration (Virtual LSP didChange + $/lean/fileProgress or batch lake env lean).
// Scoped Unicode policy (INV-001; typographic-free by default).

import { spawn, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { isWholeTheoremProof, isSafeProofReplacement, stripLeanCommentsAndStrings } from "./lean_source.ts";
import { AutoSlimJournal, contentHash, assertNoSymlinkComponents } from "./autoslim_checkpoint.ts";
import { verifyProofGroups } from "./autoslim_engine.ts";
import {
  isLakeRoot,
  leanInvocationEnv,
  planLeanInvocation,
  resolveProjectRoot,
  leanEnvironmentFingerprint,
  type LeanContext,
} from "./project_root.ts";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

export interface LspPosition {
  line: number;
  character: number;
}

export interface LspRange {
  start: LspPosition;
  end: LspPosition;
}

export interface AutoSlimCandidate {
  theoremName: string;
  route: string;
  range: LspRange;
  primaryReplacement: string;
  candidateTactics: string[];
  message: string;
}

export interface AutoSlimVerifiedEdit {
  theoremName: string;
  route: string;
  range: LspRange;
  oldText: string;
  newText: string;
  oldBytes: number;
  newBytes: number;
  oldLines: number;
  newLines: number;
  linesSaved: number;
  bytesSaved: number;
}

export interface AutoSlimRejectedCandidate {
  theoremName: string;
  route: string;
  range: LspRange;
  reason: string;
  triedTactics: string[];
  lastDiagnostic?: string;
}

export interface AutoSlimReport {
  schemaVersion: 1;
  filePath: string;
  leanRoot: string;
  backendUsed: "lsp" | "batch" | "none";
  applied: boolean;
  dryRun: boolean;
  altProofAvailable: boolean;
  importInserted: boolean;
  candidatesDiscovered: number;
  candidatesConsidered: number;
  candidatesDeferred: number;
  verifiedCount: number;
  rejectedCount: number;
  linesBefore: number;
  linesAfter: number;
  netLinesSaved: number;
  bytesBefore: number;
  bytesAfter: number;
  netBytesSaved: number;
  edits: AutoSlimVerifiedEdit[];
  rejected: AutoSlimRejectedCandidate[];
  diff: string;
  sourceHashBefore: string;
  sourceHashAfter: string;
  signaturesPreserved: boolean;
  verificationAttempts: number;
  verificationTimeMs: number;
  elapsedMs: number;
  completed: boolean;
  stopReason?: "attempt-budget" | "final-check-failed" | "verification-inconclusive";
  stopDiagnostic?: string;
  checkpointPath: string | null;
  resumedCandidates: number;
  interruptedAttempts: number;
  cacheHits: number;
  groupChecks: number;
  bisections: number;
  finalCheckPassed: boolean | null;
  provisionalCount: number;
  screenedOutCount: number;
  rankingObservations: import("./autoslim_ranking.ts").RankingObservation[];
}

export interface AutoSlimOptions {
  filePath: string;
  apply?: boolean;
  mode?: "auto" | "lsp" | "batch";
  allowAltProofImport?: boolean;
  routes?: string[];
  maxCandidates?: number;
  timeoutMs?: number;
  format?: "json" | "markdown";
  analyzerBin?: string;
  leanContext?: LeanContext;
  checkpointDir?: string;
  resume?: boolean;
  groupSize?: number;
  maxVerificationAttempts?: number;
  rankBySize?: boolean;
  rankingHistoryPath?: string;
  /** Optional Virtual LSP verifier callback injected by FileWorkerManager. */
  lspVerifier?: (candidateContent: string, timeoutMs: number) => Promise<{
    ok: boolean;
    errorCount: number;
    warningCount: number;
    firstIssue?: string;
    inconclusive?: boolean;
  }>;
}

/** A stat fingerprint of compiled inputs; generated journals and scratch files are excluded. */
function compiledInputsFingerprint(leanRoot: string, context?: LeanContext, extraRoots: string[] = []): string {
  const roots = new Set<string>([path.join(leanRoot, ".lake/build/lib/lean"), ...(context?.moduleRoots || []), ...extraRoots]);
  const manifestPath = path.join(leanRoot, "lake-manifest.json");
  if (fs.existsSync(manifestPath)) {
    const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
    for (const pkg of manifest.packages || []) {
      const directory = pkg.type === "path" && typeof pkg.dir === "string"
        ? path.resolve(leanRoot, pkg.dir) : path.join(leanRoot, ".lake/packages", String(pkg.name));
      roots.add(path.join(directory, ".lake/build/lib/lean"));
    }
  }
  const files: string[] = [];
  const seen = new Set<string>();
  const visit = (directory: string) => {
    if (!fs.existsSync(directory)) return;
    const real = fs.realpathSync(directory);
    if (seen.has(real)) return;
    seen.add(real);
    for (const entry of fs.readdirSync(real, { withFileTypes: true })) {
      const p = path.join(real, entry.name);
      const stat = entry.isSymbolicLink() ? fs.statSync(p) : undefined;
      if (entry.isDirectory() || stat?.isDirectory()) visit(p);
      else if ((entry.isFile() || stat?.isFile()) && /\.olean(?:\.private|\.server)?$/.test(entry.name)) {
        const s = fs.statSync(p, { bigint: true });
        files.push(JSON.stringify([p, String(s.size), String(s.mtimeNs), String(s.ctimeNs), String(s.ino)]));
      }
    }
  };
  for (const root of roots) visit(root);
  return contentHash(files.sort().join("\n"));
}

function verificationContext(leanRoot: string, options: AutoSlimOptions, backend: string): () => string {
  const invocation = planLeanInvocation(leanRoot, ["--print-prefix"], options.leanContext);
  let compiler = options.leanContext?.compilerPath;
  if (!compiler) {
    const probe = spawnSync(invocation.command, invocation.args, {
      cwd: invocation.cwd, env: leanInvocationEnv(invocation), encoding: "utf8", timeout: 15000,
    });
    if (probe.status === 0) {
      const prefix = probe.stdout.trim().split(/\r?\n/).at(-1) || "";
      const binary = path.join(prefix, "bin", process.platform === "win32" ? "lean.exe" : "lean");
      if (path.isAbsolute(prefix) && fs.existsSync(binary)) compiler = fs.realpathSync(binary);
    }
  }
  const policyFiles = ["autoslim", "autoslim_engine", "autoslim_checkpoint", "lean_source"].map(name => {
    const p = path.join(__dirname, name + (fs.existsSync(path.join(__dirname, name + ".ts")) ? ".ts" : ".js"));
    return contentHash(fs.readFileSync(p));
  });
  const analyzer = resolveLeanAnalyzerBin(options.analyzerBin);
  const analyzerHash = analyzer ? contentHash(fs.readFileSync(analyzer)) : "unavailable";
  const effectiveRoots = (leanInvocationEnv(invocation).LEAN_PATH || "").split(path.delimiter).filter(Boolean).map(p => path.resolve(invocation.cwd,p));
  if (compiler) effectiveRoots.push(path.join(path.dirname(path.dirname(compiler)), "lib/lean"));
  return () => {
    let compilerIdentity: unknown = "unavailable";
    if (compiler) {
      const s = fs.statSync(compiler, { bigint: true });
      compilerIdentity = [compiler, String(s.size), String(s.mtimeNs), String(s.ctimeNs), String(s.ino)];
    }
    return contentHash(JSON.stringify({
      environment: leanEnvironmentFingerprint(leanRoot, invocation.command, invocation.args, process.env, options.leanContext),
      inputs: compiledInputsFingerprint(leanRoot, options.leanContext, effectiveRoots), compilerIdentity,
      analyzerHash, policyFiles, backend, timeout: options.timeoutMs ?? 25000,
      routes: options.routes || [], allowAltProofImport: options.allowAltProofImport === true,
    }));
  };
}

export interface AutoSlimBatchReport {
  schemaVersion: 1;
  kind: "batch";
  completed: boolean;
  filesRequested: number;
  filesApplied: number;
  verifiedCount: number;
  rejectedCount: number;
  verificationTimeMs: number;
  elapsedMs: number;
  reports: AutoSlimReport[];
  failures: { filePath: string; error: string }[];
}

export function formatAutoSlimBatchMarkdown(report: AutoSlimBatchReport): string {
  return [`# Batch fixes: ${report.reports.length}/${report.filesRequested} files processed`,
    ...report.reports.map(formatAutoSlimMarkdown),
    ...report.failures.map(f => `Failed: ${f.filePath}: ${f.error}`)].join("\n\n");
}

/** Tactics defined in ProofSkills/AltProof.lean (or re-exported by a project Tactics.lean umbrella). */
export const ALTPROOF_CUSTOM_TACTICS = new Set<string>([
  "sum_congr_ring",
  "calc_ring_sum",
  "finset_nonneg",
  "finset_mono",
  "convex_comb",
  "markov_row_sum",
  "matrix_pos",
  "gcongr_pos",
  "wellformed_tac",
  "channel_fields",
  "eqsat_rw",
  "egg_rw",
  "backchain",
  "contra_direct",
  "grind_close",
  "sair_decide",
  "elegance?",
  "bfs_elegance?",
  "alt_proof",
]);

/** Ranked tactic cascade per canonical altproof route (custom AltProof closers -> Mathlib/Core fallbacks). */
export const ROUTE_TACTIC_CASCADES: Record<string, readonly string[]> = {
  "kernel-friendly-term-design": ["by grind", "by omega", "by aesop", "by simp_all", "by simp", "by nlinarith", "by linarith", "by norm_num", "by ring"],
  sum_congr_ring: ["by sum_congr_ring", "by markov_row_sum", "by calc_ring_sum", "by convex_comb", "by ring_nf", "by simp"],
  finset_nonneg: ["by finset_nonneg", "by matrix_pos", "by convex_comb", "by positivity"],
  finset_mono: ["by finset_mono", "by convex_comb", "by gcongr_pos"],
  "eqsat-congruence-closure": ["by eqsat_rw", "by grind_close", "by grind", "by simp"],
  "backchain-solve-by-elim": ["by backchain", "by solve_by_elim", "by aesop"],
  "redirect-by-contradiction": ["by contra_direct", "by decide"],
  "uniform-simp-collapse": [
    "by simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, \u2193reduceIte]",
    "by simp",
  ],
  bv_decide: ["by bv_decide", "by decide"],
  sair_decide: ["by sair_decide", "by decide"],
};

/** Resolve the bundled or workspace `lean-analyzer` binary path. */
export function resolveLeanAnalyzerBin(explicitBin?: string): string | null {
  const candidates = [
    explicitBin || "",
    process.env.LEAN_ANALYZER_BIN || "",
    path.resolve(__dirname, "../bin/lean-analyzer"),
    path.resolve(__dirname, "../../../crates/lean-analyzer/target/release/lean-analyzer"),
    path.resolve(__dirname, "../../../target/release/lean-analyzer"),
    path.join(os.homedir(), ".local", "bin", "lean-analyzer"),
  ].filter(Boolean);
  for (const cand of candidates) {
    try {
      if (fs.existsSync(cand) && fs.statSync(cand).isFile()) {
        return cand;
      }
    } catch {
      // ignore unreadable candidate
    }
  }
  return null;
}

/** Compute line start offsets (in JS UTF-16 code units) for a document string. */
export function computeUtf16LineOffsets(text: string): number[] {
  const offsets: number[] = [0];
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) === 10) {
      offsets.push(i + 1);
    }
  }
  return offsets;
}

/** Convert a 0-based LSP `{ line, character }` (UTF-16 code units) into a JS string index. */
export function lspPositionToStringIndex(
  text: string,
  lineOffsets: readonly number[],
  pos: LspPosition
): number | null {
  if (!Number.isInteger(pos.line) || !Number.isInteger(pos.character)) return null;
  if (pos.line < 0 || pos.line >= lineOffsets.length || pos.character < 0) return null;
  const lineStart = lineOffsets[pos.line];
  let lineEnd = pos.line + 1 < lineOffsets.length ? lineOffsets[pos.line + 1] - 1 : text.length;
  if (lineEnd > lineStart && text.charCodeAt(lineEnd - 1) === 13) {
    lineEnd--;
  }
  const idx = lineStart + pos.character;
  if (idx > lineEnd) return null;
  return idx;
}

/** Extract `[startIdx, endIdx]` in JS UTF-16 string indices for an LSP `range`. */
export function lspRangeToStringOffsets(
  text: string,
  lineOffsets: readonly number[],
  range: LspRange
): { startIdx: number; endIdx: number } | null {
  const startIdx = lspPositionToStringIndex(text, lineOffsets, range.start);
  const endIdx = lspPositionToStringIndex(text, lineOffsets, range.end);
  if (startIdx === null || endIdx === null || endIdx < startIdx) return null;
  return { startIdx, endIdx };
}

/** Check whether a candidate replacement invokes an `AltProof` custom tactic. */
export function requiresAltProofTactic(tacticSnippet: string): boolean {
  const body = tacticSnippet.trim().replace(/^by\s+/, "").trim();
  const head = body.split(/[\s;(\[]/)[0] || "";
  return ALTPROOF_CUSTOM_TACTICS.has(head);
}

/**
 * Inspect whether a Lean file already has `AltProof` tactics in scope, or whether the
 * enclosing Lake project provides `AltProof.lean` / `<Project>/Tactics.lean` for optional import.
 *
 * Dynamically discovers `<Pkg>/Tactics.lean` or `<Pkg>/AltProof.lean` inside `leanRoot`
 * (and `lakefile.toml` / `lakefile.lean` local `path` dependencies) without hardcoding
 * private project names.
 */
export function detectAltProofAvailability(
  sourceText: string,
  leanRoot: string
): {
  importedInFile: boolean;
  availableModule: string | null;
} {
  const importRe = /^\s*import\s+([A-Za-z0-9_.']+)/gm;
  const directImports: string[] = [];
  let m: RegExpExecArray | null;
  while ((m = importRe.exec(sourceText)) !== null) {
    directImports.push(m[1]);
  }

  // Collect Lake search roots: leanRoot itself + any relative `path = "..."` dependency roots
  const searchRoots: string[] = [leanRoot];
  for (const lf of ["lakefile.toml", "lakefile.lean"]) {
    const lfPath = path.join(leanRoot, lf);
    try {
      if (fs.existsSync(lfPath)) {
        const lfText = fs.readFileSync(lfPath, "utf-8");
        const pathMatches = lfText.matchAll(/(?:path\s*=\s*|from\s+)"([^"]+)"/g);
        for (const pm of pathMatches) {
          const resolvedDep = path.resolve(leanRoot, pm[1]);
          if (fs.existsSync(resolvedDep) && !searchRoots.includes(resolvedDep)) {
            searchRoots.push(resolvedDep);
          }
        }
      }
    } catch {
      // ignore unreadable lakefile
    }
  }

  const fileProvidesAltProof = (absFile: string): boolean => {
    try {
      if (!fs.existsSync(absFile)) return false;
      const txt = fs.readFileSync(absFile, "utf-8");
      return (
        /\b(?:elab|macro)\s+"?(?:sum_congr_ring|finset_mono|finset_nonneg|convex_comb|markov_row_sum|matrix_pos|eqsat_rw|grind_close|solve_by_elim_bounded)\b/.test(
          txt
        ) || /\bimport\s+[A-Za-z0-9_.']*AltProof\b/.test(txt)
      );
    } catch {
      return false;
    }
  };

  for (const imp of directImports) {
    if (imp === "AltProof" || imp.endsWith(".AltProof") || imp === "ProofSkills.AltProof") {
      return { importedInFile: true, availableModule: imp };
    }
    const modRel = imp.split(".").join(path.sep) + ".lean";
    for (const sr of searchRoots) {
      const mc = path.join(sr, modRel);
      try {
        if (fs.existsSync(mc)) {
          if (imp.endsWith(".Tactics") && fileProvidesAltProof(mc)) {
            return { importedInFile: true, availableModule: imp };
          }
          const subSrc = fs.readFileSync(mc, "utf-8");
          const subImportRe = /^\s*import\s+([A-Za-z0-9_.']+)/gm;
          let sm: RegExpExecArray | null;
          while ((sm = subImportRe.exec(subSrc)) !== null) {
            const subImp = sm[1];
            if (subImp === "AltProof" || subImp.endsWith(".AltProof")) {
              return { importedInFile: true, availableModule: imp };
            }
            if (subImp.endsWith(".Tactics")) {
              const subRel = subImp.split(".").join(path.sep) + ".lean";
              if (searchRoots.some((r) => fileProvidesAltProof(path.join(r, subRel)))) {
                return { importedInFile: true, availableModule: imp };
              }
            }
          }
        }
      } catch {
        // ignore
      }
    }
  }

  // Discover any importable AltProof or <Pkg>.Tactics module across searchRoots
  for (const sr of searchRoots) {
    const directCandidates: Array<[string, string]> = [
      ["ProofSkills.AltProof", path.join(sr, "ProofSkills", "AltProof.lean")],
      ["AltProof", path.join(sr, "AltProof.lean")],
    ];
    for (const [modName, p] of directCandidates) {
      if (fs.existsSync(p)) {
        return { importedInFile: false, availableModule: modName };
      }
    }
    try {
      const entries = fs.readdirSync(sr, { withFileTypes: true });
      for (const ent of entries) {
        if (!ent.isDirectory() || ent.name.startsWith(".") || ent.name === "build") continue;
        const altPath = path.join(sr, ent.name, "AltProof.lean");
        const tacPath = path.join(sr, ent.name, "Tactics.lean");
        const tacAltPath = path.join(sr, ent.name, "Tactics", "AltProof.lean");
        if (fs.existsSync(tacPath) && fileProvidesAltProof(tacPath)) {
          return { importedInFile: false, availableModule: `${ent.name}.Tactics` };
        }
        if (fs.existsSync(altPath)) {
          return { importedInFile: false, availableModule: `${ent.name}.AltProof` };
        }
        if (fs.existsSync(tacAltPath)) {
          return { importedInFile: false, availableModule: `${ent.name}.Tactics.AltProof` };
        }
      }
    } catch {
      // ignore
    }
  }

  return { importedInFile: false, availableModule: null };
}

/** Insert `import <moduleName>` right after the last top-of-file `import ...` line. */
export function insertModuleImport(sourceText: string, moduleName: string): string {
  const lines = sourceText.split("\n");
  let lastImportIdx = -1;
  for (let i = 0; i < lines.length; i++) {
    const t = lines[i].trim();
    if (t.startsWith("import ")) {
      lastImportIdx = i;
    } else if (
      t.length > 0 &&
      !t.startsWith("--") &&
      !t.startsWith("/-") &&
      !t.startsWith("-/") &&
      !t.startsWith("*") &&
      lastImportIdx >= 0
    ) {
      break;
    }
  }
  if (lastImportIdx >= 0) {
    lines.splice(lastImportIdx + 1, 0, `import ${moduleName}`);
    return lines.join("\n");
  }
  return `import ${moduleName}\n${sourceText}`;
}

/** Build ordered, deduplicated tactic replacement list for a discovered `ALTPROOF-ROUTE` candidate. */
export function buildCandidateTacticList(
  route: string,
  primaryReplacement: string,
  allowCustomAltProof: boolean
): string[] {
  const ordered: string[] = [];
  const push = (raw: string) => {
    const norm = raw.trim().startsWith("by ") ? raw.trim() : `by ${raw.trim()}`;
    if (!norm || ordered.includes(norm)) return;
    if (!allowCustomAltProof && requiresAltProofTactic(norm)) return;
    ordered.push(norm);
  };
  if (primaryReplacement) push(primaryReplacement);
  const cascade = ROUTE_TACTIC_CASCADES[route] || [];
  for (const c of cascade) push(c);
  return ordered;
}

/** Preserve explicit definition hints when replacing a structural proof as a whole. */
export function buildUnfoldingTactics(proof: string): string[] {
  const names = new Set<string>();
  for (const match of stripLeanCommentsAndStrings(proof).matchAll(/\bunfold[ \t]+([^;\n]+)/g)) {
    const args = match[1].split(/\s+at\b/)[0].trim().split(/\s+/);
    if (args.every(name => /^[\p{L}_][\p{L}\p{N}_'.]*$/u.test(name))) {
      for (const name of args) names.add(name);
    }
  }
  if (names.size === 0) return [];
  const defs = [...names].join(", ");
  return [`by simp_all [${defs}]`, `by grind [${defs}]`, `by simp [${defs}]`];
}

/** Discover `ALTPROOF-ROUTE` quickfix candidates on `absPath` via `lean-analyzer lint --format=json`. */
export function discoverAutoSlimCandidates(
  absPath: string,
  options: {
    analyzerBin?: string;
    routes?: string[];
    allowCustomAltProof: boolean;
  }
): AutoSlimCandidate[] {
  const bin = resolveLeanAnalyzerBin(options.analyzerBin);
  if (!bin) {
    throw new Error(
      "lean-analyzer binary not found; build crates/lean-analyzer or set LEAN_ANALYZER_BIN"
    );
  }
  const proc = spawnSync(bin, ["lint", absPath, "--format=json"], {
    encoding: "utf-8",
    maxBuffer: 16 * 1024 * 1024,
    timeout: 30000,
  });
  if (proc.status !== 0) {
    throw new Error(
      `lean-analyzer lint failed (exit ${proc.status}): ${(proc.stderr || proc.stdout || "").trim()}`
    );
  }
  const parsed = JSON.parse(proc.stdout);
  const fileEntry = Array.isArray(parsed?.files) ? parsed.files[0] : null;
  const diags: any[] = Array.isArray(fileEntry?.diagnostics) ? fileEntry.diagnostics : [];
  const routeFilter =
    options.routes && options.routes.length > 0 ? new Set(options.routes) : null;

  const candidates: AutoSlimCandidate[] = [];
  for (const d of diags) {
    if (d?.code !== "ALTPROOF-ROUTE" || !d?.quickfix?.range) continue;
    const route = String(d.altproof_route || "").trim();
    if (routeFilter && !routeFilter.has(route)) continue;
    const primaryReplacement = String(d.quickfix.new_text || "").trim();
    const candidateTactics = buildCandidateTacticList(
      route,
      primaryReplacement,
      options.allowCustomAltProof
    );
    if (candidateTactics.length === 0) continue;
    candidates.push({
      theoremName: String(d.operator || "unknown"),
      route,
      range: {
        start: {
          line: Number(d.quickfix.range.start?.line ?? 0),
          character: Number(d.quickfix.range.start?.character ?? 0),
        },
        end: {
          line: Number(d.quickfix.range.end?.line ?? 0),
          character: Number(d.quickfix.range.end?.character ?? 0),
        },
      },
      primaryReplacement,
      candidateTactics,
      message: String(d.message || ""),
    });
  }
  return candidates;
}

/** Run `lake env lean <scratchPath>` (or admitted compiler) with process-group timeout protection. */
export function runBatchLeanCheck(
  leanRoot: string,
  targetDirForScratch: string,
  candidateContent: string,
  timeoutMs: number,
  leanContext?: LeanContext
): Promise<{
  ok: boolean;
  errorCount: number;
  warningCount: number;
  firstIssue?: string;
  inconclusive?: boolean;
}> {
  const scratchName = `.autoslim_probe_${process.pid}_${Date.now()}_${Math.random()
    .toString(36)
    .slice(2, 8)}.lean`;
  const scratchPath = path.join(targetDirForScratch, scratchName);
  fs.writeFileSync(scratchPath, candidateContent, "utf-8");

  const invocation = planLeanInvocation(leanRoot, ["-DwarningAsError=true", scratchPath], leanContext);
  const env = leanInvocationEnv(invocation);

  return new Promise((resolve) => {
    let stdout = "";
    let stderr = "";
    let finished = false;
    let timedOut = false;

    let child;
    try {
      child = spawn(invocation.command, invocation.args, {
        cwd: invocation.cwd,
        env,
        stdio: ["ignore", "pipe", "pipe"],
        detached: true,
      });
    } catch (err: any) {
      try {
        fs.unlinkSync(scratchPath);
      } catch {
        // ignore
      }
      resolve({
        ok: false,
        errorCount: 1,
        warningCount: 0,
        firstIssue: `spawn failed: ${err?.message || String(err)}`,
        inconclusive: true,
      });
      return;
    }

    const timer = setTimeout(() => {
      if (finished) return;
      timedOut = true;
      try {
        if (child.pid !== undefined) process.kill(-child.pid, "SIGKILL");
        else child.kill("SIGKILL");
      } catch {
        try {
          child.kill("SIGKILL");
        } catch {
          // ignore
        }
      }
    }, Math.max(1000, timeoutMs));

    const finalize = (code: number | null) => {
      if (finished) return;
      finished = true;
      clearTimeout(timer);
      try {
        fs.unlinkSync(scratchPath);
      } catch {
        // ignore
      }
      const combined = `${stdout}\n${stderr}`.trim();
      if (timedOut) {
        resolve({
          ok: false,
          errorCount: 1,
          warningCount: 0,
          firstIssue: `timeout after ${timeoutMs}ms`,
          inconclusive: true,
        });
        return;
      }
      const errorMatches = combined.match(/:\d+:\d+:\s*error\b/g) || [];
      const warnMatches = combined.match(/:\d+:\d+:\s*warning\b/g) || [];
      const hasSorryWarn = /\bdeclaration uses 'sorry'\b/.test(combined);
      const errorCount = errorMatches.length + (code !== 0 && errorMatches.length === 0 ? 1 : 0);
      const warningCount = warnMatches.length + (hasSorryWarn && warnMatches.length === 0 ? 1 : 0);
      const ok = code === 0 && errorCount === 0 && warningCount === 0;
      const firstLine = combined
        .split(/\r?\n/)
        .map((l) => l.trim())
        .find((l) => l.length > 0);
      resolve({
        ok,
        errorCount,
        warningCount,
        ...(ok ? {} : { firstIssue: firstLine || `exit code ${code}` }),
      });
    };

    child.stdout?.on("data", (d: Buffer) => {
      stdout += d.toString("utf-8");
    });
    child.stderr?.on("data", (d: Buffer) => {
      stderr += d.toString("utf-8");
    });
    child.on("error", (err: Error) => {
      stderr += `\nspawn failed: ${err.message}`;
      finalize(1);
    });
    child.on("close", (code: number | null) => finalize(code));
  });
}

/** Build a compact unified diff snippet for human/audit review. */
export function buildCompactUnifiedDiff(
  relPath: string,
  beforeText: string,
  afterText: string
): string {
  if (beforeText === afterText) return "";
  const beforeLines = beforeText.split("\n");
  const afterLines = afterText.split("\n");
  const hunks: string[] = [`--- a/${relPath}`, `+++ b/${relPath}`];

  let i = 0;
  let j = 0;
  while (i < beforeLines.length || j < afterLines.length) {
    if (i < beforeLines.length && j < afterLines.length && beforeLines[i] === afterLines[j]) {
      i++;
      j++;
      continue;
    }
    const startI = i;
    const startJ = j;
    // Advance until 2 consecutive matching lines re-sync
    let foundSync = false;
    for (let lookI = i; lookI <= Math.min(beforeLines.length, i + 80) && !foundSync; lookI++) {
      for (let lookJ = j; lookJ <= Math.min(afterLines.length, j + 80); lookJ++) {
        const m1 =
          lookI < beforeLines.length &&
          lookJ < afterLines.length &&
          beforeLines[lookI] === afterLines[lookJ];
        const m2 =
          lookI + 1 >= beforeLines.length && lookJ + 1 >= afterLines.length
            ? true
            : lookI + 1 < beforeLines.length &&
              lookJ + 1 < afterLines.length &&
              beforeLines[lookI + 1] === afterLines[lookJ + 1];
        if (m1 && m2) {
          i = lookI;
          j = lookJ;
          foundSync = true;
          break;
        }
      }
    }
    if (!foundSync) {
      i = beforeLines.length;
      j = afterLines.length;
    }
    const oldCount = i - startI;
    const newCount = j - startJ;
    hunks.push(`@@ -${startI + 1},${oldCount} +${startJ + 1},${newCount} @@`);
    for (let k = startI; k < i; k++) hunks.push(`-${beforeLines[k]}`);
    for (let k = startJ; k < j; k++) hunks.push(`+${afterLines[k]}`);
  }
  return hunks.join("\n");
}

/** Check INV-001 typographic-free safety on synthesized edits (no curly quotes, em-dashes, or invisible carriers). */
export function hasForbiddenUnicode(text: string): boolean {
  return /[\u00A0\u200B-\u200F\u2013\u2014\u2018-\u201F\u2026\u202A-\u202E\u202F\u2066-\u2069\uFEFF]/.test(
    text
  );
}

/**
 * Execute kernel-verified proof auto-slimming on a single `.lean` file.
 * Supports Virtual LSP (`lspVerifier`) and `lake env lean` (`batch`) verification,
 * accumulating accepted edits sequentially so cross-theorem interactions are caught.
 */
export async function runKernelVerifiedAutoSlim(
  projectRoot: string,
  options: AutoSlimOptions
): Promise<AutoSlimReport> {
  const startedAt = performance.now();
  const absPath = path.isAbsolute(options.filePath)
    ? path.resolve(options.filePath)
    : path.resolve(projectRoot, options.filePath);
  if (!fs.existsSync(absPath)) {
    throw new Error(`File not found: ${options.filePath}`);
  }
  const lstat = fs.lstatSync(absPath);
  assertNoSymlinkComponents(absPath);
  if (lstat.isSymbolicLink() || !lstat.isFile()) {
    throw new Error(`Refusing non-regular or symlinked target: ${options.filePath}`);
  }

  const resolvedRoot = resolveProjectRoot(path.dirname(absPath), {}, projectRoot);
  const leanRoot =
    resolvedRoot.source === "none" ? path.resolve(projectRoot) : resolvedRoot.root;

  const originalBytes = fs.readFileSync(absPath);
  const originalText = originalBytes.toString("utf8");
  if (!Buffer.from(originalText, "utf8").equals(originalBytes)) {
    throw new Error("Refusing invalid UTF-8 source; original bytes are unchanged");
  }
  const hash = (text: string) => createHash("sha256").update(text).digest("hex");
  const sourceHashBefore = hash(originalText);
  const assertSourceUnchanged = () => {
    const stat = fs.lstatSync(absPath);
    if (!stat.isFile() || stat.isSymbolicLink() || stat.ino !== lstat.ino || stat.dev !== lstat.dev
      || !fs.readFileSync(absPath).equals(originalBytes)) {
      throw new Error("Source changed during auto-slimming; refusing stale edits");
    }
  };
  const linesBefore = originalText.split("\n").length;
  const bytesBefore = Buffer.byteLength(originalText, "utf-8");

  const avail = detectAltProofAvailability(originalText, leanRoot);
  const allowCustomAltProof =
    avail.importedInFile || (options.allowAltProofImport === true && avail.availableModule !== null);

  const rawCandidates = discoverAutoSlimCandidates(absPath, {
    analyzerBin: options.analyzerBin,
    routes: options.routes,
    allowCustomAltProof,
  });
  assertSourceUnchanged();

  const maxCandidates = Math.max(1, Math.min(200, Number(options.maxCandidates ?? 50)));
  const timeoutMs = Math.max(2000, Math.min(120000, Number(options.timeoutMs ?? 25000)));
  const mode = options.mode || "auto";
  const apply = options.apply === true;

  if (rawCandidates.length === 0) {
    return {
      schemaVersion: 1,
      filePath: absPath,
      leanRoot,
      backendUsed: "none",
      applied: false,
      dryRun: !apply,
      altProofAvailable: allowCustomAltProof,
      importInserted: false,
      candidatesDiscovered: 0,
      candidatesConsidered: 0,
      candidatesDeferred: 0,
      verifiedCount: 0,
      rejectedCount: 0,
      linesBefore,
      linesAfter: linesBefore,
      netLinesSaved: 0,
      bytesBefore,
      bytesAfter: bytesBefore,
      netBytesSaved: 0,
      edits: [],
      rejected: [],
      diff: "",
      sourceHashBefore,
      sourceHashAfter: sourceHashBefore,
      signaturesPreserved: true,
      verificationAttempts: 0,
      verificationTimeMs: 0,
      elapsedMs: performance.now() - startedAt,
      completed: true,
      checkpointPath: null,
      resumedCandidates: 0,
      interruptedAttempts: 0,
      cacheHits: 0,
      groupChecks: 0,
      bisections: 0,
      finalCheckPassed: null,
      provisionalCount: 0,
      screenedOutCount: 0,
      rankingObservations: [],
    };
  }

  const useLsp =
    (mode === "lsp" || mode === "auto") && typeof options.lspVerifier === "function";
  if (mode === "lsp" && !useLsp) {
    throw new Error("mode='lsp' requested, but no Virtual LSP verifier is available");
  }
  if (!useLsp && !options.leanContext && !isLakeRoot(leanRoot)) {
    throw new Error(
      `Cannot run batch Lean verification outside a Lake project without LeanContext (${leanRoot})`
    );
  }
  const backendUsed: "lsp" | "batch" = useLsp ? "lsp" : "batch";
  const currentContext = verificationContext(leanRoot, options, backendUsed);
  const contextFingerprint = currentContext();
  const identity = contentHash(JSON.stringify([absPath, sourceHashBefore, contextFingerprint]));
  const journal = new AutoSlimJournal(path.resolve(options.checkpointDir || path.join(leanRoot, ".lake/autoslim-checkpoints")), identity, options.resume === false);
  const interruptedAttempts = journal.pendingAttempts.size;
  const groupSize = options.groupSize ?? 4;
  if (!Number.isInteger(groupSize) || groupSize < 1 || groupSize > 32) throw new Error("groupSize must be an integer in 1..32");
  if (options.maxVerificationAttempts !== undefined && (!Number.isInteger(options.maxVerificationAttempts) || options.maxVerificationAttempts < 0)) {
    throw new Error("maxVerificationAttempts must be a nonnegative integer");
  }

  let verificationAttempts = 0;
  let verificationTimeMs = 0;
  const verifyContent = async (content: string) => {
    assertSourceUnchanged();
    if (currentContext() !== contextFingerprint) throw new Error("Verification context changed; checkpoint cannot authorize source writes");
    const start = performance.now();
    verificationAttempts++;
    const verdict = useLsp ? await options.lspVerifier!(content, timeoutMs) : await runBatchLeanCheck(
      leanRoot,
      path.dirname(absPath),
      content,
      timeoutMs,
      options.leanContext
    );
    verificationTimeMs += performance.now() - start;
    assertSourceUnchanged();
    if (currentContext() !== contextFingerprint) throw new Error("Verification context changed during compilation");
    return verdict;
  };

  // Map candidates onto exact original-buffer character intervals, filtering invalid or overlapping spans
  const origLineOffsets = computeUtf16LineOffsets(originalText);
  interface IndexedCandidate {
    cand: AutoSlimCandidate;
    origStart: number;
    origEnd: number;
    oldSlice: string;
    id: string;
    tactics: string[];
    score: number;
  }

  const validIndexed: IndexedCandidate[] = [];
  const rejected: AutoSlimRejectedCandidate[] = [];

  for (const cand of rawCandidates) {
    const offs = lspRangeToStringOffsets(originalText, origLineOffsets, cand.range);
    if (!offs) {
      rejected.push({
        theoremName: cand.theoremName,
        route: cand.route,
        range: cand.range,
        reason: "invalid-lsp-range",
        triedTactics: [],
      });
      continue;
    }
    const oldSlice = originalText.slice(offs.startIdx, offs.endIdx);
    if (!isWholeTheoremProof(originalText, offs.startIdx, offs.endIdx, cand.theoremName)) {
      rejected.push({ theoremName: cand.theoremName, route: cand.route, range: cand.range,
        reason: "proof-boundary-or-declaration-mismatch", triedTactics: [] });
      continue;
    }
    if (!/^by\b/.test(oldSlice)) {
      rejected.push({
        theoremName: cand.theoremName,
        route: cand.route,
        range: cand.range,
        reason: "span-does-not-start-with-by",
        triedTactics: [],
      });
      continue;
    }
    if (/\bsorry\b|\badmit\b/.test(stripLeanCommentsAndStrings(oldSlice))) {
      rejected.push({
        theoremName: cand.theoremName,
        route: cand.route,
        range: cand.range,
        reason: "contains-sorry-or-admit",
        triedTactics: [],
      });
      continue;
    }
    if (
      validIndexed.some(
        (prev) => !(offs.endIdx <= prev.origStart || offs.startIdx >= prev.origEnd)
      )
    ) {
      rejected.push({
        theoremName: cand.theoremName,
        route: cand.route,
        range: cand.range,
        reason: "overlapping-quickfix-span",
        triedTactics: [],
      });
      continue;
    }
    const oldLines = oldSlice.split("\n").length;
    const oldBytes = Buffer.byteLength(oldSlice);
    const tactics = [...new Set([...buildUnfoldingTactics(oldSlice), ...cand.candidateTactics])].filter(tac =>
      isSafeProofReplacement(tac) && !hasForbiddenUnicode(tac)
      && (tac.split("\n").length < oldLines || (tac.split("\n").length === oldLines && Buffer.byteLength(tac) < oldBytes)));
    if (tactics.length === 0) {
      rejected.push({ theoremName: cand.theoremName, route: cand.route, range: cand.range,
        reason: "no-safe-shorter-recipe", triedTactics: [] });
      continue;
    }
    validIndexed.push({
      cand,
      origStart: offs.startIdx,
      origEnd: offs.endIdx,
      oldSlice,
      tactics,
      id: contentHash(JSON.stringify([cand.theoremName, cand.route, offs.startIdx, offs.endIdx, oldSlice, tactics])),
      score: (oldLines - 1) * 1_000_000_000 + oldBytes - Math.min(...tactics.map(t => Buffer.byteLength(t))),
    });
  }

  const history = readRankingHistory(options.rankingHistoryPath);
  for (const item of validIndexed) {
    item.tactics = rankTactics(item.cand.route, item.tactics, history);
    item.id = contentHash(JSON.stringify([item.cand.theoremName, item.cand.route, item.origStart, item.origEnd, item.oldSlice, [...item.tactics].sort()]));
    item.score = candidatePriority(item.cand.route, item.score, history);
  }
  const screenedOutCount = rejected.length;
  const ranked = [...validIndexed].sort(options.rankBySize === false
    ? (a, b) => a.origStart - b.origStart : (a, b) => b.score - a.score || a.origStart - b.origStart);
  const selected = ranked.slice(0, maxCandidates);
  const selectedById = new Map(selected.map(item => [item.id, item]));
  const render = (choices: ReadonlyMap<string, string>): string => {
    let text = originalText;
    const ordered = [...choices].map(([id, tactic]) => {
      const item = selectedById.get(id);
      if (!item || !item.tactics.includes(tactic)) throw new Error("Checkpoint recipe is outside the rediscovered candidate set");
      return { item, tactic };
    }).sort((a, b) => b.item.origStart - a.item.origStart);
    for (const { item, tactic } of ordered) {
      if (text.slice(item.origStart, item.origEnd) !== item.oldSlice) throw new Error("Proof span drift during grouped rendering");
      text = text.slice(0, item.origStart) + tactic + text.slice(item.origEnd);
    }
    if (!avail.importedInFile && avail.availableModule && options.allowAltProofImport === true
      && ordered.some(({ tactic }) => requiresAltProofTactic(tactic))) {
      text = insertModuleImport(text, avail.availableModule);
    }
    return text;
  };
  const grouped = await verifyProofGroups({
    proposals: selected.map(item => ({ id: item.id, tactics: item.tactics })),
    render, verify: verifyContent, journal, groupSize, maxAttempts: options.maxVerificationAttempts,
  });
  for (const [id, failure] of grouped.rejected) {
    const item = selectedById.get(id)!;
    rejected.push({ theoremName: item.cand.theoremName, route: item.cand.route,
      range: item.cand.range, reason: "kernel-rejected", ...failure });
  }
  const edits: AutoSlimVerifiedEdit[] = [];
  let workingText = originalText;
  let importInserted = false;
  if (grouped.completed && grouped.finalCheckPassed === true) {
    workingText = render(grouped.accepted);
    for (const item of [...selected].sort((a, b) => a.origStart - b.origStart)) {
      const tactic = grouped.accepted.get(item.id);
      if (tactic === undefined) continue;
      const oldBytes = Buffer.byteLength(item.oldSlice);
      const newBytes = Buffer.byteLength(tactic);
      const oldLines = item.oldSlice.split("\n").length;
      const newLines = tactic.split("\n").length;
      edits.push({ theoremName: item.cand.theoremName, route: item.cand.route,
        range: item.cand.range, oldText: item.oldSlice, newText: tactic,
        oldBytes, newBytes, oldLines, newLines, linesSaved: oldLines - newLines, bytesSaved: oldBytes - newBytes });
    }
    importInserted = !avail.importedInFile && !!avail.availableModule
      && [...grouped.accepted.values()].some(requiresAltProofTactic);
  }

  let applied = false;
  if (apply && edits.length > 0 && workingText !== originalText) {
    assertSourceUnchanged();
    if (currentContext() !== contextFingerprint) throw new Error("Verification context changed before publication");
    if (hasForbiddenUnicode(workingText) && !hasForbiddenUnicode(originalText)) {
      throw new Error("Refusing to write auto-slimmed file: synthesized content violates INV-001 Unicode policy");
    }
    const modeBits = lstat.mode & 0o777;
    const tmpDir = fs.mkdtempSync(path.join(path.dirname(absPath), ".autoslim_apply_"));
    const tmpWritePath = path.join(tmpDir, "source.lean");
    try {
      fs.writeFileSync(tmpWritePath, workingText, { encoding: "utf-8", mode: modeBits, flag: "wx" });
      assertSourceUnchanged();
      fs.renameSync(tmpWritePath, absPath);
    } finally {
      if (fs.existsSync(tmpWritePath)) fs.unlinkSync(tmpWritePath);
      fs.rmdirSync(tmpDir);
    }
    applied = true;
  }

  const linesAfter = workingText.split("\n").length;
  const bytesAfter = Buffer.byteLength(workingText, "utf-8");
  const relPath = path.relative(leanRoot, absPath) || path.basename(absPath);
  const diff = buildCompactUnifiedDiff(relPath, originalText, workingText);

  return {
    schemaVersion: 1,
    filePath: absPath,
    leanRoot,
    backendUsed,
    applied,
    dryRun: !applied,
    altProofAvailable: allowCustomAltProof,
    importInserted,
    candidatesDiscovered: rawCandidates.length,
    candidatesConsidered: selected.length,
    candidatesDeferred: Math.max(0, validIndexed.length - selected.length),
    verifiedCount: edits.length,
    rejectedCount: rejected.length,
    linesBefore,
    linesAfter,
    netLinesSaved: linesBefore - linesAfter,
    bytesBefore,
    bytesAfter,
    netBytesSaved: bytesBefore - bytesAfter,
    edits,
    rejected,
    diff,
    sourceHashBefore,
    sourceHashAfter: hash(workingText),
    signaturesPreserved: true,
    verificationAttempts,
    verificationTimeMs,
    elapsedMs: performance.now() - startedAt,
    completed: grouped.completed,
    ...(grouped.stopReason ? { stopReason: grouped.stopReason } : {}),
    ...(grouped.stopDiagnostic ? { stopDiagnostic: grouped.stopDiagnostic } : {}),
    checkpointPath: journal.filePath,
    resumedCandidates: grouped.resumedCandidates,
    interruptedAttempts,
    cacheHits: grouped.cacheHits,
    groupChecks: grouped.groupChecks,
    bisections: grouped.bisections,
    finalCheckPassed: grouped.finalCheckPassed,
    provisionalCount: grouped.completed ? 0 : grouped.accepted.size,
    screenedOutCount,
    rankingObservations: grouped.observations.map(o => ({route:selectedById.get(o.id)!.cand.route,tactic:o.tactic,ok:o.ok,elapsedMs:o.elapsedMs})),
  };
}

export function formatAutoSlimMarkdown(report: AutoSlimReport): string {
  const lines: string[] = [
    `# Auto-Slim Report: \`${path.basename(report.filePath)}\``,
    `- **File**: \`${report.filePath}\``,
    `- **Backend**: \`${report.backendUsed}\` (\`applied=${report.applied}\`, \`altProofAvailable=${report.altProofAvailable}\`${report.importInserted ? ", inserted AltProof import" : ""})`,
    `- **Candidates**: ${report.verifiedCount} verified / ${report.candidatesDiscovered} discovered (${report.rejectedCount} rejected)`,
    `- **Coverage**: ${report.candidatesConsidered} considered; ${report.candidatesDeferred} deferred`,
    `- **Progress**: completed=${report.completed}, ${report.resumedCandidates} resumed, ${report.cacheHits} cache hits, ${report.bisections} bisections; final check=${report.finalCheckPassed}`,
    `- **LOC Impact**: ${report.linesBefore} -> ${report.linesAfter} lines (**net -${report.netLinesSaved} LOC**, -${report.netBytesSaved} bytes)`,
    `- **Verification**: ${report.verificationAttempts} attempts, ${report.verificationTimeMs.toFixed(1)} ms; public signatures preserved`,
  ];
  if (report.edits.length > 0) {
    lines.push("", "## Verified Slimmed Proofs");
    for (const e of report.edits) {
      lines.push(
        `- **\`${e.theoremName}\`** [\`${e.route}\`, L${e.range.start.line + 1}-L${e.range.end.line + 1}]: \`${e.newText}\` (-${e.linesSaved} lines, -${e.bytesSaved} B)`
      );
    }
  }
  if (report.rejected.length > 0) {
    lines.push("", "## Rejected Candidates");
    for (const r of report.rejected) {
      lines.push(
        `- **\`${r.theoremName}\`** [\`${r.route}\`]: ${r.reason}${r.triedTactics.length ? ` (tried: ${r.triedTactics.map((t) => `\`${t}\``).join(", ")})` : ""}${r.lastDiagnostic ? ` -- ${r.lastDiagnostic}` : ""}`
      );
    }
  }
  if (report.diff) {
    lines.push("", "## Unified Diff", "```diff", report.diff, "```");
  }
  return lines.join("\n");
}
