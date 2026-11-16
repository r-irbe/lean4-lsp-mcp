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
import {
  isLakeRoot,
  leanInvocationEnv,
  planLeanInvocation,
  resolveProjectRoot,
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
  /** Optional Virtual LSP verifier callback injected by FileWorkerManager. */
  lspVerifier?: (candidateContent: string, timeoutMs: number) => Promise<{
    ok: boolean;
    errorCount: number;
    warningCount: number;
    firstIssue?: string;
  }>;
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
}> {
  const scratchName = `.autoslim_probe_${process.pid}_${Date.now()}_${Math.random()
    .toString(36)
    .slice(2, 8)}.lean`;
  const scratchPath = path.join(targetDirForScratch, scratchName);
  fs.writeFileSync(scratchPath, candidateContent, "utf-8");

  const invocation = planLeanInvocation(leanRoot, [scratchPath], leanContext);
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
      stderr += `\n${err.message}`;
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
  const absPath = path.isAbsolute(options.filePath)
    ? path.resolve(options.filePath)
    : path.resolve(projectRoot, options.filePath);
  if (!fs.existsSync(absPath)) {
    throw new Error(`File not found: ${options.filePath}`);
  }
  const lstat = fs.lstatSync(absPath);
  if (lstat.isSymbolicLink() || !lstat.isFile()) {
    throw new Error(`Refusing non-regular or symlinked target: ${options.filePath}`);
  }

  const resolvedRoot = resolveProjectRoot(path.dirname(absPath), {}, projectRoot);
  const leanRoot =
    resolvedRoot.source === "none" ? path.resolve(projectRoot) : resolvedRoot.root;

  const originalText = fs.readFileSync(absPath, "utf-8");
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

  const verifyContent = async (content: string) => {
    if (useLsp) {
      return await options.lspVerifier!(content, timeoutMs);
    }
    return await runBatchLeanCheck(
      leanRoot,
      path.dirname(absPath),
      content,
      timeoutMs,
      options.leanContext
    );
  };

  // Map candidates onto exact original-buffer character intervals, filtering invalid or overlapping spans
  const origLineOffsets = computeUtf16LineOffsets(originalText);
  interface IndexedCandidate {
    cand: AutoSlimCandidate;
    origStart: number;
    origEnd: number;
    oldSlice: string;
  }

  const validIndexed: IndexedCandidate[] = [];
  const rejected: AutoSlimRejectedCandidate[] = [];

  for (const cand of rawCandidates.slice(0, maxCandidates)) {
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
    if (/\bsorry\b|\badmit\b/.test(oldSlice)) {
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
    validIndexed.push({
      cand,
      origStart: offs.startIdx,
      origEnd: offs.endIdx,
      oldSlice,
    });
  }

  // Sort top-to-bottom and track cumulative delta (plus optional import insertion delta)
  validIndexed.sort((a, b) => a.origStart - b.origStart);

  let workingText = originalText;
  let importDelta = 0;
  let importInserted = false;
  let cumulativeEditDelta = 0;
  const edits: AutoSlimVerifiedEdit[] = [];

  for (const item of validIndexed) {
    const { cand, origStart, origEnd, oldSlice } = item;
    const oldBytes = Buffer.byteLength(oldSlice, "utf-8");
    const oldLines = oldSlice.split("\n").length;
    const triedTactics: string[] = [];
    let lastDiag: string | undefined;
    let acceptedEdit: AutoSlimVerifiedEdit | null = null;

    for (const tac of cand.candidateTactics) {
      if (hasForbiddenUnicode(tac)) continue;
      const newBytes = Buffer.byteLength(tac, "utf-8");
      const newLines = tac.split("\n").length;
      // Strict slimming invariant: must strictly reduce lines, or keep 1 line with strictly fewer bytes
      const strictlySlimmer =
        newLines < oldLines || (newLines === oldLines && newBytes < oldBytes);
      if (!strictlySlimmer) continue;

      let baseText = workingText;
      let localImportDelta = importDelta;
      let needsImportNow = false;
      if (
        !avail.importedInFile &&
        !importInserted &&
        requiresAltProofTactic(tac) &&
        options.allowAltProofImport === true &&
        avail.availableModule
      ) {
        const withImp = insertModuleImport(workingText, avail.availableModule);
        localImportDelta = withImp.length - workingText.length;
        baseText = withImp;
        needsImportNow = true;
      }

      const curStart = origStart + (needsImportNow ? localImportDelta : importDelta) + cumulativeEditDelta;
      const curEnd = origEnd + (needsImportNow ? localImportDelta : importDelta) + cumulativeEditDelta;
      if (baseText.slice(curStart, curEnd) !== oldSlice) {
        lastDiag = "span-drift-mismatch";
        break;
      }

      triedTactics.push(tac);
      const trialContent = baseText.slice(0, curStart) + tac + baseText.slice(curEnd);
      const verdict = await verifyContent(trialContent);
      if (verdict.ok) {
        workingText = trialContent;
        if (needsImportNow) {
          importInserted = true;
          importDelta = localImportDelta;
        }
        cumulativeEditDelta += tac.length - oldSlice.length;
        acceptedEdit = {
          theoremName: cand.theoremName,
          route: cand.route,
          range: cand.range,
          oldText: oldSlice,
          newText: tac,
          oldBytes,
          newBytes,
          oldLines,
          newLines,
          linesSaved: oldLines - newLines,
          bytesSaved: oldBytes - newBytes,
        };
        break;
      } else {
        lastDiag = verdict.firstIssue;
      }
    }

    if (acceptedEdit) {
      edits.push(acceptedEdit);
    } else {
      rejected.push({
        theoremName: cand.theoremName,
        route: cand.route,
        range: cand.range,
        reason: triedTactics.length === 0 ? "not-strictly-shorter" : "kernel-rejected",
        triedTactics,
        ...(lastDiag ? { lastDiagnostic: lastDiag } : {}),
      });
    }
  }

  let applied = false;
  if (apply && edits.length > 0 && workingText !== originalText) {
    if (hasForbiddenUnicode(workingText) && !hasForbiddenUnicode(originalText)) {
      throw new Error("Refusing to write auto-slimmed file: synthesized content violates INV-001 Unicode policy");
    }
    const modeBits = lstat.mode & 0o777;
    const tmpWritePath = path.join(
      path.dirname(absPath),
      `.autoslim_apply_${process.pid}_${createHash("sha256")
        .update(absPath)
        .digest("hex")
        .slice(0, 8)}.tmp`
    );
    fs.writeFileSync(tmpWritePath, workingText, { encoding: "utf-8", mode: modeBits });
    fs.renameSync(tmpWritePath, absPath);
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
  };
}

export function formatAutoSlimMarkdown(report: AutoSlimReport): string {
  const lines: string[] = [
    `# Kernel-Verified Auto-Slim Report: \`${path.basename(report.filePath)}\``,
    `- **File**: \`${report.filePath}\``,
    `- **Backend**: \`${report.backendUsed}\` (\`applied=${report.applied}\`, \`altProofAvailable=${report.altProofAvailable}\`${report.importInserted ? ", inserted AltProof import" : ""})`,
    `- **Candidates**: ${report.verifiedCount} verified / ${report.candidatesDiscovered} discovered (${report.rejectedCount} rejected)`,
    `- **LOC Impact**: ${report.linesBefore} -> ${report.linesAfter} lines (**net -${report.netLinesSaved} LOC**, -${report.netBytesSaved} bytes)`,
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
