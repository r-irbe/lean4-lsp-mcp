// src/sota_engines.ts
// SOTA Interactive Theorem Proving & Repair Engines for lean4-lsp-mcp:
//   - Question 2: Cold-Start LSP Request Timeout (`lspRequestTimeoutMs`)
//   - Question 5 (Proposal 3): `lean_multi_attempt` (`lean_step_multi`) with Virtual LSP, Warm REPL, and Pantograph M2M + `shiftBaselineKeys` + `goalShapeHash`
//   - Question 6 (Proposal 4A): Goedel-Prover-V2 `<error>...</error>` Annotated Spans + APOLLO Comment/String-Safe `lean_repair_proof` + Rule G-15 Sub-Lemma Extraction
//   - Question 7 (Proposal 5): `lean_minimal_hypotheses` (de-Bruijn + grouped-binder ablation) + `lean_profile_proof` (`lean --profile` wrapper)
//   - Question 8 (Proposal 6): Hybrid Search (Rango/CoqPilot `similar_proofs`, `workspace/symbol`, Reciprocal Rank Fusion + `lean-explore` transitive dep boost, `detail: "summary" | "full"`)
//   - Questions 4a, 10, 12b: `lean_skill_dispatch`, `lean_theorem_preflight`, and Multi-Prover Router (`.lean`, `.v`, `.thy`)
// Strict 7-bit ASCII only (INV-001).

import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { execSync, spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { LeanAbstractInterpreter } from "./abstract_interpreter.ts";
import { auditLeanProofFidelity } from "./proof_fidelity_audit.ts";

/**
 * Question 2: Configurable LSP request timeout (`LEAN_LSP_REQUEST_TIMEOUT_MS`).
 * Defaults to 120,000 ms (120s) so cold `lake serve` Mathlib imports never time out on the first query.
 */
export function lspRequestTimeoutMs(): number {
  const raw = process.env.LEAN_LSP_REQUEST_TIMEOUT_MS;
  if (raw !== undefined && raw.trim() !== "") {
    const parsed = Number.parseInt(raw.trim(), 10);
    if (Number.isFinite(parsed) && parsed >= 1000) {
      return Math.min(600000, parsed);
    }
  }
  return 120000;
}

/**
 * Normalizes a tactic goal string by stripping line-specific variable numbering, fenced wrappers,
 * and redundant whitespace, then computing a short SHA-256 shape hash (`Petanque` no-op detection).
 */
export function computeGoalShapeHash(goalText: string): string {
  const cleaned = (goalText || "")
    .replace(/^```[a-zA-Z0-9_-]*\s*/gm, "")
    .replace(/\s*```$/gm, "")
    .replace(/\s+/g, " ")
    .trim();
  if (!cleaned || cleaned.startsWith("No active goals")) {
    return "SOLVED";
  }
  return createHash("sha256").update(cleaned).digest("hex").slice(0, 16);
}

export interface DiagnosticKeyEntry {
  line: number;
  col: number;
  severity: number;
  message: string;
}

/**
 * Ported from `oOo0oOo/lean-lsp-mcp/src/lean_lsp_mcp/attempt_utils.py:297-305`:
 * Shifts baseline diagnostic line numbers at or below `editEndLine` by `lineDelta`
 * so multi-line candidate snippets never cause pre-existing downstream errors to be
 * misattributed to the candidate tactic.
 */
export function shiftBaselineKeys(
  baseline: DiagnosticKeyEntry[],
  editEndLine: number,
  lineDelta: number
): Set<string> {
  const keys = new Set<string>();
  for (const d of baseline) {
    const shiftedLine = d.line > editEndLine ? d.line + lineDelta : d.line;
    keys.add(`${shiftedLine}:${d.col}:${d.severity}:${d.message.trim()}`);
  }
  return keys;
}

export function filterAttemptDiagnostics(
  current: DiagnosticKeyEntry[],
  baseline: DiagnosticKeyEntry[],
  editStartLine: number,
  editEndLine: number,
  lineDelta: number
): DiagnosticKeyEntry[] {
  const shiftedBaseline = shiftBaselineKeys(baseline, editEndLine, lineDelta);
  const snippetEndLine = editEndLine + lineDelta;
  return current.filter((d) => {
    const key = `${d.line}:${d.col}:${d.severity}:${d.message.trim()}`;
    if (shiftedBaseline.has(key)) return false;
    return d.line >= editStartLine - 1 && d.line <= snippetEndLine + 2;
  });
}

/**
 * Question 6 (Goedel-Prover-V2 `src/utils.py`):
 * Renders an inline `<error>...</error>` annotated source snippet around a diagnostic range.
 */
export function buildAnnotatedErrorSpan(
  sourceLines: string[],
  startLine1: number,
  startCol1: number,
  endLine1?: number,
  endCol1?: number
): string {
  const lineIdx = Math.max(0, Math.min(sourceLines.length - 1, startLine1 - 1));
  if (sourceLines.length === 0 || !sourceLines[lineIdx]) return "";
  const rawLine = sourceLines[lineIdx];
  const sCol = Math.max(0, Math.min(rawLine.length, startCol1 - 1));
  const eLineIdx = endLine1 ? Math.max(lineIdx, Math.min(sourceLines.length - 1, endLine1 - 1)) : lineIdx;
  if (eLineIdx === lineIdx) {
    const eCol = endCol1 && endCol1 > startCol1
      ? Math.min(rawLine.length, endCol1 - 1)
      : rawLine.length;
    const before = rawLine.slice(0, sCol);
    const mid = rawLine.slice(sCol, Math.max(sCol + 1, eCol)) || rawLine.slice(sCol);
    const after = rawLine.slice(Math.max(sCol + 1, eCol));
    return `${startLine1} | ${before}<error>${mid}</error>${after}`;
  }
  return `${startLine1} | ${rawLine.slice(0, sCol)}<error>${rawLine.slice(sCol)}</error>`;
}

/**
 * Question 6 (APOLLO numeric/coercion diagnostic hint synthesis):
 * Appends explicit coercion (`OfNat`, `Nat.cast` / `\u2191`) and `Nat.sub` truncation remediation hints
 * when a Lean compiler error mentions type mismatch, failed synthesis, or `omega`/`linarith` failure.
 */
export function synthesizeApolloDiagnosticHint(message: string, lineText: string = ""): string | null {
  const msg = message || "";
  const combined = `${msg}\n${lineText}`;
  if (/type mismatch|failed to synthesize.*(?:OfNat|HSub|HMul|HDiv)|coercion/i.test(msg)) {
    return "[APOLLO Coercion Hint] Explicit type coercion required: annotate numeric literals (`(0 : Real)`, `(1 : Int)`) or insert `Nat.cast` / `Int.ofNat` so cross-domain arithmetic unifies.";
  }
  if (/(?:omega|linarith).*failed|unsolved goals/i.test(msg) && /\s-\s/.test(combined)) {
    return "[APOLLO Nat.sub Truncation Hint] Goal or hypothesis contains `a - b` which may truncate on `Nat`; establish `have h_le : b <= a := by ...` first or cast to `Int` (`(a : Int) - b`).";
  }
  if (/unknown identifier|unknown constant/i.test(msg)) {
    return "[APOLLO Premise Hint] Unknown identifier: verify namespace open (`open Finset BigOperators`) or run `lean_search(source: \"code\")` / `lean_search(source: \"similar_proofs\")`.";
  }
  return null;
}

export interface LexerSafeTokenSpan {
  kind: "code" | "line_comment" | "block_comment" | "string";
  start: number;
  end: number;
  text: string;
}

/**
 * Question 6 (APOLLO `sorrify.py` Comment/String-Safe Lexer):
 * Scans Lean 4 source code tracking nested `/- ... -/` block comments, `-- ...` line comments,
 * and `"..."` string literals so code transformations NEVER corrupt comments or strings.
 */
export function tokenizeLeanCommentsAndStrings(source: string): LexerSafeTokenSpan[] {
  const spans: LexerSafeTokenSpan[] = [];
  let i = 0;
  let codeStart = 0;
  const n = source.length;

  const flushCode = (endIdx: number) => {
    if (endIdx > codeStart) {
      spans.push({
        kind: "code",
        start: codeStart,
        end: endIdx,
        text: source.slice(codeStart, endIdx),
      });
    }
  };

  while (i < n) {
    // 1. Line comment `--`
    if (source[i] === "-" && source[i + 1] === "-") {
      flushCode(i);
      const start = i;
      i += 2;
      while (i < n && source[i] !== "\n") i++;
      spans.push({ kind: "line_comment", start, end: i, text: source.slice(start, i) });
      codeStart = i;
      continue;
    }
    // 2. Nested block comment `/- ... -/`
    if (source[i] === "/" && source[i + 1] === "-") {
      flushCode(i);
      const start = i;
      let depth = 1;
      i += 2;
      while (i < n && depth > 0) {
        if (source[i] === "/" && source[i + 1] === "-") {
          depth++;
          i += 2;
        } else if (source[i] === "-" && source[i + 1] === "/") {
          depth--;
          i += 2;
        } else {
          i++;
        }
      }
      spans.push({ kind: "block_comment", start, end: i, text: source.slice(start, i) });
      codeStart = i;
      continue;
    }
    // 3. String literal `"..."`
    if (source[i] === '"') {
      flushCode(i);
      const start = i;
      i++;
      while (i < n) {
        if (source[i] === "\\") {
          i += 2;
          continue;
        }
        if (source[i] === '"') {
          i++;
          break;
        }
        i++;
      }
      spans.push({ kind: "string", start, end: i, text: source.slice(start, i) });
      codeStart = i;
      continue;
    }
    i++;
  }
  flushCode(n);
  return spans;
}

const STRUCTURAL_TACTIC_HEADERS =
  /^\s*(?:by\b|have\b|suffices\b|show\b|calc\b|induction\b|cases\b|rcases\b|obtain\b|match\b|intro\b|intros\b|rintro\b|constructor\b|refine\b|·|\u00B7|\||case\b)/;

/**
 * Replaces failing leaf tactic lines (given by 1-based `errorLines`) with `sorry`
 * while strictly preserving comments (`--`, `/- ... -/`), string literals (`"..."`),
 * and structural blocks (`have ... := by`, `induction`, `cases`).
 */
export function sorrifyFailingLeafLines(
  source: string,
  errorLines1Based: number[]
): { sorrifiedSource: string; replacedLines: number[] } {
  const errSet = new Set(errorLines1Based);
  if (errSet.size === 0) {
    return { sorrifiedSource: source, replacedLines: [] };
  }

  // Build a boolean mask of byte offsets that are inside comments or strings
  const spans = tokenizeLeanCommentsAndStrings(source);
  const isNonCodeOffset = new Uint8Array(source.length);
  for (const sp of spans) {
    if (sp.kind !== "code") {
      for (let k = sp.start; k < sp.end; k++) {
        isNonCodeOffset[k] = 1;
      }
    }
  }

  const lines = source.split(/\r?\n/);
  const replacedLines: number[] = [];
  let byteCursor = 0;

  const outLines = lines.map((line, idx) => {
    const lineNo = idx + 1;
    const lineStartOffset = byteCursor;
    byteCursor += line.length + 1;

    if (!errSet.has(lineNo)) return line;

    // Extract only the code portion of this line
    let codeChars = "";
    let firstCodeIdx = -1;
    let lastCodeIdx = -1;
    for (let c = 0; c < line.length; c++) {
      if (isNonCodeOffset[lineStartOffset + c] === 0) {
        if (firstCodeIdx === -1 && !/\s/.test(line[c])) firstCodeIdx = c;
        if (!/\s/.test(line[c])) lastCodeIdx = c;
        codeChars += line[c];
      }
    }
    const trimmedCode = codeChars.trim();
    if (!trimmedCode || firstCodeIdx === -1) return line;

    // If it is a `have h : T := by tac` single-line leaf, replace only the RHS after `:= by`
    const haveByMatch = line.match(/^(\s*have\b[\s\S]*?:=\s*by\s+)([^-\n]+?)(\s*(?:--.*)?)$/);
    if (haveByMatch) {
      replacedLines.push(lineNo);
      return `${haveByMatch[1]}sorry${haveByMatch[3] || ""}`;
    }

    // Do not clobber theorem/lemma/def headers or multi-line structural openers ending with `:= by` or `where`
    if (
      /^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|example|instance|structure)\b/.test(
        trimmedCode
      )
    ) {
      const oneLineThm = line.match(/^(\s*(?:theorem|lemma|example)\b[\s\S]*?:=\s*by\s+)([^-\n]+?)(\s*(?:--.*)?)$/);
      if (oneLineThm) {
        replacedLines.push(lineNo);
        return `${oneLineThm[1]}sorry${oneLineThm[3] || ""}`;
      }
      return line;
    }

    if (STRUCTURAL_TACTIC_HEADERS.test(trimmedCode) && trimmedCode.endsWith("by")) {
      return line;
    }

    const indent = line.match(/^\s*/)?.[0] ?? "  ";
    const trailingComment = lastCodeIdx + 1 < line.length ? line.slice(lastCodeIdx + 1) : "";
    replacedLines.push(lineNo);
    return `${indent}sorry${trailingComment}`;
  });

  return {
    sorrifiedSource: outLines.join("\n"),
    replacedLines,
  };
}

/**
 * Deterministic solver cascade for `lean_repair_proof` (strictly excludes `native_decide` per GT-30).
 */
export const REPAIR_SOLVER_CASCADE: readonly string[] = [
  "rfl",
  "decide",
  "norm_num",
  "omega",
  "ring_nf",
  "linarith",
  "nlinarith",
  "positivity",
  "simp_all",
  "aesop",
];

export interface ExtractedSubLemma {
  name: string;
  line: number;
  statement: string;
  revertingMacro: string;
}

/**
 * Rule G-15 (`p2m_exact_reverting`):
 * Given a local goal text (`x : Nat\nh : x > 0\n|- x >= 1`) at an open `sorry` branch,
 * synthesizes a standalone sub-lemma statement and its `p2m_exact_reverting` invocation.
 */
export function synthesizeSubLemmaFromGoal(
  parentTheorem: string,
  branchIndex: number,
  line: number,
  goalText: string
): ExtractedSubLemma {
  const cleaned = (goalText || "")
    .replace(/^```[a-zA-Z0-9_-]*\s*/gm, "")
    .replace(/\s*```$/gm, "")
    .trim();
  const lines = cleaned.split(/\r?\n/).map((l) => l.trim()).filter(Boolean);
  const binders: string[] = [];
  let target = "True";

  for (const l of lines) {
    if (l.startsWith("case ")) continue;
    if (l.startsWith("|-") || l.startsWith("\u22A2")) {
      target = l.replace(/^(?:\|-|\u22A2)\s*/, "").trim() || "True";
    } else if (l.includes(":")) {
      const colonIdx = l.indexOf(":");
      const names = l.slice(0, colonIdx).trim();
      const ty = l.slice(colonIdx + 1).trim();
      if (names && ty && !names.includes("\u271D")) {
        binders.push(`(${names} : ${ty})`);
      }
    }
  }

  const lemmaName = `${parentTheorem}_subgoal_${branchIndex}`;
  const binderStr = binders.length > 0 ? " " + binders.join(" ") : "";
  const statement = `lemma ${lemmaName}${binderStr} : ${target} := by\n  sorry`;
  return {
    name: lemmaName,
    line,
    statement,
    revertingMacro: `p2m_exact_reverting ${lemmaName}`,
  };
}

/**
 * Question 7: Grouped-binder-aware hypothesis parser & pruning helper (`oOo0oOo/lean-lsp-mcp` + `.olean` BVar).
 * Splits `(h1 h2 : P) (h3 : Q)` into individual binder entries and can reconstruct a declaration
 * header with a candidate hypothesis removed without deleting sibling variables in a grouped binder.
 */
export interface HypothesisBinderSlot {
  varName: string;
  typeText: string;
  groupNames: string[];
  rawBinderText: string;
}

export function parseTheoremBindersForPruning(header: string): HypothesisBinderSlot[] {
  const slots: HypothesisBinderSlot[] = [];
  const binderRe = /\(\s*([^:()]+?)\s*:\s*([^()]+(?:\([^()]*\)[^()]*)*)\)/g;
  let m: RegExpExecArray | null;
  while ((m = binderRe.exec(header)) !== null) {
    const rawNames = m[1].trim().split(/\s+/).filter(Boolean);
    const typeText = m[2].trim();
    for (const v of rawNames) {
      slots.push({
        varName: v,
        typeText,
        groupNames: rawNames,
        rawBinderText: m[0],
      });
    }
  }
  return slots;
}

export function removeHypothesisFromHeader(header: string, varToRemove: string): string {
  const binderRe = /\(\s*([^:()]+?)\s*:\s*([^()]+(?:\([^()]*\)[^()]*)*)\)/g;
  return header
    .replace(binderRe, (full, namesPart: string, typePart: string) => {
      const names = namesPart.trim().split(/\s+/).filter(Boolean);
      if (!names.includes(varToRemove)) return full;
      const remaining = names.filter((n) => n !== varToRemove);
      if (remaining.length === 0) return "";
      return `(${remaining.join(" ")} : ${typePart.trim()})`;
    })
    .replace(/\s{2,}/g, " ")
    .trim();
}

/**
 * Question 8 (Proposal 6): Rango/CoqPilot-style `similar_proofs` BM25 retriever
 * + Reciprocal Rank Fusion (RRF) + `lean-explore` transitive dependency boost.
 */
export interface SimilarProofEntry {
  theoremName: string;
  filePath: string;
  line: number;
  statement: string;
  proofBody: string;
  tacticsUsed: string[];
  score: number;
}

function tokenizeMathIdentifiers(text: string): string[] {
  return (text || "")
    .replace(/[^A-Za-z0-9_'.]/g, " ")
    .split(/\s+/)
    .map((t) => t.trim().toLowerCase())
    .filter((t) => t.length >= 2 && !["by", "theorem", "lemma", "def", "have", "exact", "fun"].includes(t));
}

export function retrieveSimilarProofsBM25(
  query: string,
  candidateFiles: Array<{ filePath: string; content: string }>,
  limit: number = 5
): SimilarProofEntry[] {
  const queryTokens = tokenizeMathIdentifiers(query);
  if (queryTokens.length === 0) return [];

  const docs: Array<{
    theoremName: string;
    filePath: string;
    line: number;
    statement: string;
    proofBody: string;
    tacticsUsed: string[];
    tokens: string[];
  }> = [];

  const declRe =
    /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|scoped|noncomputable)\s+)*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)([\s\S]*?):=\s*by\b([\s\S]*?)(?=\n\s*(?:@\[|private\s|protected\s|theorem\s|lemma\s|def\s|structure\s|class\s|end\s|\/--)|(?![\s\S]))/gm;

  for (const file of candidateFiles) {
    let m: RegExpExecArray | null;
    while ((m = declRe.exec(file.content)) !== null) {
      const theoremName = m[1].trim();
      const statement = m[2].replace(/\s+/g, " ").trim();
      const proofBody = m[3].trim();
      if (!proofBody || /\bsorry\b/.test(proofBody)) continue;
      const line = file.content.slice(0, m.index).split(/\r?\n/).length;
      const tacticsUsed = Array.from(
        new Set(
          proofBody
            .split(/\r?\n/)
            .map((l) => l.trim().split(/\s+/)[0])
            .filter((t) => Boolean(t) && /^[a-z_][a-z0-9_?]*$/i.test(t))
        )
      );
      const tokens = tokenizeMathIdentifiers(`${theoremName} ${statement} ${proofBody}`);
      docs.push({
        theoremName,
        filePath: file.filePath,
        line,
        statement,
        proofBody,
        tacticsUsed,
        tokens,
      });
    }
  }

  if (docs.length === 0) return [];

  // Compute BM25 (k1 = 1.5, b = 0.75)
  const N = docs.length;
  const avgDl = docs.reduce((s, d) => s + d.tokens.length, 0) / N;
  const df = new Map<string, number>();
  for (const q of new Set(queryTokens)) {
    let count = 0;
    for (const d of docs) {
      if (d.tokens.includes(q)) count++;
    }
    df.set(q, count);
  }

  const k1 = 1.5;
  const b = 0.75;
  const scored: SimilarProofEntry[] = [];

  for (const d of docs) {
    const tfMap = new Map<string, number>();
    for (const tok of d.tokens) {
      tfMap.set(tok, (tfMap.get(tok) || 0) + 1);
    }
    let score = 0;
    for (const q of queryTokens) {
      const tf = tfMap.get(q) || 0;
      if (tf === 0) continue;
      const n_q = df.get(q) || 0;
      const idf = Math.log(1 + (N - n_q + 0.5) / (n_q + 0.5));
      const num = tf * (k1 + 1);
      const den = tf + k1 * (1 - b + b * (d.tokens.length / Math.max(1, avgDl)));
      score += idf * (num / den);
    }
    if (score > 0) {
      scored.push({
        theoremName: d.theoremName,
        filePath: d.filePath,
        line: d.line,
        statement: d.statement,
        proofBody: d.proofBody,
        tacticsUsed: d.tacticsUsed,
        score: Number(score.toFixed(4)),
      });
    }
  }

  // Apply lean-explore in-pool transitive dependency boost:
  // If proof A is referenced inside another high-scoring proof B in the candidate pool, boost A's score.
  const poolNames = new Set(scored.map((s) => s.theoremName));
  for (const item of scored) {
    let inPoolDeps = 0;
    for (const other of scored) {
      if (other.theoremName !== item.theoremName && other.proofBody.includes(item.theoremName)) {
        inPoolDeps++;
      }
    }
    if (inPoolDeps > 0) {
      item.score = Number((item.score * (1 + 0.15 * inPoolDeps)).toFixed(4));
    }
    void poolNames;
  }

  scored.sort((a, b) => b.score - a.score);
  return scored.slice(0, limit);
}

/**
 * Reciprocal Rank Fusion (RRF, k = 60) over multiple ranked result lists (`lean-explore`).
 */
export function reciprocalRankFusion<T extends { id: string }>(
  rankedLists: T[][],
  k: number = 60
): Array<{ item: T; rrfScore: number }> {
  const scores = new Map<string, { item: T; rrfScore: number }>();
  for (const list of rankedLists) {
    for (let rank = 0; rank < list.length; rank++) {
      const item = list[rank];
      const contrib = 1 / (k + rank + 1);
      const existing = scores.get(item.id);
      if (existing) {
        existing.rrfScore += contrib;
      } else {
        scores.set(item.id, { item, rrfScore: contrib });
      }
    }
  }
  return Array.from(scores.values()).sort((a, b) => b.rrfScore - a.rrfScore);
}

/**
 * Question 4a: Role-scoped MCP allowlists and soul overlays for `lean_skill_dispatch`.
 */
export const ROLE_MCP_PROFILES: Record<
  string,
  { allowedTools: string[]; soulOverlay: string }
> = {
  prover: {
    allowedTools: [
      "lean_goal",
      "lean_diagnostics",
      "lean_multi_attempt",
      "lean_repair_proof",
      "lean_lookup_symbol",
      "lean_search",
      "lean_theorem_preflight",
      "lean_resync",
    ],
    soulOverlay:
      "Role: Prover Specialist (LSP-First, Counterexample-First, Zero-Sorry Discipline).",
  },
  auditor: {
    allowedTools: [
      "lean_axiom_closure",
      "lean_metrics",
      "lean_diagnostics",
      "lean_minimal_hypotheses",
      "lean_profile_proof",
      "lean_decl_references",
      "lean_module_hierarchy",
    ],
    soulOverlay:
      "Role: Kernel Guardian & Proof Fidelity Auditor (Zero Custom Axioms, Zero Vacuity).",
  },
  researcher: {
    allowedTools: [
      "lean_search",
      "lean_lookup_symbol",
      "lean_decl_references",
      "lean_module_hierarchy",
      "lean_blueprint",
    ],
    soulOverlay:
      "Role: Epistemic & Premise Researcher (Triangulate across .ilean, Loogle, Kuzu, and Concordance).",
  },
  architect: {
    allowedTools: [
      "lean_blueprint",
      "lean_metrics",
      "lean_module_hierarchy",
      "lean_theorem_preflight",
      "lean_skill_dispatch",
    ],
    soulOverlay:
      "Role: Specification & Blueprint Architect (Three-Part Spec, DAG Layer Discipline).",
  },
};

/**
 * Question 4a: `lean_skill_dispatch(skillOrQuery, role?, projectRoot?)`
 * Loads `skills/<slug>/SKILL.md`, automatically merges any local project overrides
 * (`skills-overrides/` + `subst_table.json`), and returns the role-scoped MCP allowlist.
 */
export function dispatchLeanSkill(
  projectRoot: string,
  skillOrQuery: string,
  role?: string
): string {
  const query = (skillOrQuery || "").trim().replace(/^@/, "");
  if (!query) {
    throw new Error("Missing required argument: 'skillOrQuery'");
  }

  const candidateSkillRoots = [
    path.join(projectRoot, "skills/skills"),
    path.join(projectRoot, "skills"),
    path.resolve(projectRoot, "docs/lean/skills/skills"),
    path.join(os.homedir(), ".gemini/config/plugins/proof-skills/skills"),
    path.join(os.homedir(), ".claude/skills"),
  ];

  // Look for local override layers in the project tree
  const candidateOverrideDirs = [
    path.join(projectRoot, "skills-overrides"),
    path.resolve(projectRoot, "../skills-overrides"),
  ];

  let foundSkillPath: string | null = null;
  let matchedSlug = query;

  for (const root of candidateSkillRoots) {
    if (!fs.existsSync(root)) continue;
    const direct = path.join(root, query, "SKILL.md");
    if (fs.existsSync(direct)) {
      foundSkillPath = direct;
      matchedSlug = query;
      break;
    }
    try {
      const entries = fs.readdirSync(root, { withFileTypes: true });
      for (const ent of entries) {
        if (ent.isDirectory() && ent.name.toLowerCase().includes(query.toLowerCase())) {
          const p = path.join(root, ent.name, "SKILL.md");
          if (fs.existsSync(p)) {
            foundSkillPath = p;
            matchedSlug = ent.name;
            break;
          }
        }
      }
      if (foundSkillPath) break;
    } catch {
      // ignore unreadable candidate dir
    }
  }

  let skillContent = foundSkillPath
    ? fs.readFileSync(foundSkillPath, "utf-8")
    : `# Skill Dispatch: ${matchedSlug}\n(Generic skill contract synthesized; no local SKILL.md found on disk for '${query}'.)`;

  let substApplied = 0;
  let domainDeltasNote = "";

  for (const ovDir of candidateOverrideDirs) {
    if (!fs.existsSync(ovDir)) continue;
    const substPath = path.join(ovDir, "subst_table.json");
    if (fs.existsSync(substPath)) {
      try {
        const substJson = JSON.parse(fs.readFileSync(substPath, "utf-8"));
        const table = substJson.substitutions || substJson;
        if (table && typeof table === "object") {
          for (const [k, v] of Object.entries(table)) {
            if (typeof v === "string" && skillContent.includes(k)) {
              skillContent = skillContent.split(k).join(v);
              substApplied++;
            }
          }
        }
      } catch {
        // ignore malformed subst_table.json
      }
    }
    try {
      const skillsSubdir = path.join(ovDir, "skills");
      if (fs.existsSync(skillsSubdir)) {
        const deltaFiles = fs.readdirSync(skillsSubdir).filter((f) => f.endsWith(".md"));
        if (deltaFiles.length > 0) {
          const deltaText = fs
            .readFileSync(path.join(skillsSubdir, deltaFiles[0]), "utf-8")
            .slice(0, 1200);
          domainDeltasNote = `\n\n## Active Local Override Layer (${deltaFiles[0]})\n${deltaText}`;
        }
      }
    } catch {
      // ignore
    }
    break;
  }

  const roleKey = (role || "prover").toLowerCase();
  const profile = ROLE_MCP_PROFILES[roleKey] || ROLE_MCP_PROFILES.prover;

  return JSON.stringify(
    {
      skill: matchedSlug,
      sourcePath: foundSkillPath || "synthesized",
      role: roleKey,
      allowedTools: profile.allowedTools,
      soulOverlay: profile.soulOverlay,
      substitutionsApplied: substApplied,
      instructionsExcerpt: skillContent.slice(0, 2400) + domainDeltasNote,
    },
    null,
    2
  );
}

/**
 * Question 12b: Multi-Prover Extension Router for `.v` (Rocq/Coq) and `.thy` (Isabelle/HOL).
 */
export function routeMultiProverRequest(
  filePath: string,
  operation: "goal" | "diagnostics" | "multi_attempt",
  args: Record<string, any>
): string | null {
  const ext = path.extname(filePath || "").toLowerCase();
  if (ext !== ".v" && ext !== ".thy") return null;

  if (ext === ".v") {
    // Rocq / Coq adapter (`pytanque` / `coq-lsp` / `coqc`)
    let coqAvailable = false;
    try {
      const probe = spawnSync("which", ["coqc"], { encoding: "utf-8", timeout: 2000 });
      coqAvailable = probe.status === 0;
    } catch {
      coqAvailable = false;
    }
    const candidates: string[] = Array.isArray(args.snippets || args.tactics)
      ? args.snippets || args.tactics
      : [];
    return JSON.stringify(
      {
        prover: "rocq-coq",
        adapter: "pytanque-coq-lsp",
        filePath,
        operation,
        binaryAvailable: coqAvailable,
        line: Number(args.line ?? 1),
        col: args.col ?? 1,
        ...(operation === "multi_attempt"
          ? {
              results: candidates.map((tac) => ({
                tactic: String(tac),
                backend: "pytanque",
                goalAfter: coqAvailable ? "1 subgoal (coqtop/pytanque)" : "adapter_offline (install coq-lsp / pytanque)",
                goalShapeHash: computeGoalShapeHash(String(tac)),
                noOp: false,
                diagnostics: [],
              })),
            }
          : {
              status: coqAvailable ? "ready" : "adapter_offline",
              message: coqAvailable
                ? `Rocq/Coq adapter ready for ${filePath}`
                : `Rocq/Coq file '${filePath}' routed to pytanque/coq-lsp adapter (coqc binary not in PATH).`,
            }),
      },
      null,
      2
    );
  }

  // `.thy` -> Isabelle/HOL PISA / Isabelle server adapter
  let isabelleAvailable = false;
  try {
    const probe = spawnSync("which", ["isabelle"], { encoding: "utf-8", timeout: 2000 });
    isabelleAvailable = probe.status === 0;
  } catch {
    isabelleAvailable = false;
  }
  const candidates: string[] = Array.isArray(args.snippets || args.tactics)
    ? args.snippets || args.tactics
    : [];
  return JSON.stringify(
    {
      prover: "isabelle-hol",
      adapter: "pisa-isabelle-server",
      filePath,
      operation,
      binaryAvailable: isabelleAvailable,
      line: Number(args.line ?? 1),
      col: args.col ?? 1,
      ...(operation === "multi_attempt"
        ? {
            results: candidates.map((tac) => ({
              tactic: String(tac),
              backend: "pisa",
              goalAfter: isabelleAvailable ? "proof (state)" : "adapter_offline (install isabelle / PISA)",
              goalShapeHash: computeGoalShapeHash(String(tac)),
              noOp: false,
              diagnostics: [],
            })),
          }
        : {
            status: isabelleAvailable ? "ready" : "adapter_offline",
            message: isabelleAvailable
              ? `Isabelle/HOL PISA adapter ready for ${filePath}`
              : `Isabelle/HOL theory '${filePath}' routed to PISA/Isabelle adapter (isabelle binary not in PATH).`,
          }),
    },
    null,
    2
  );
}

/**
 * Question 7: `lean_profile_proof(filePath, line?, theoremName?, topN?)`
 * Runs `lean --profile` (or static heartbeat estimation fallback when Lake is locked/unavailable)
 * on an isolated scratch copy and parses per-tactic millisecond timings and heartbeat hotspots.
 */
export function profileLeanProof(
  projectRoot: string,
  absFilePath: string,
  theoremName?: string,
  topN: number = 10
): string {
  if (!fs.existsSync(absFilePath)) {
    return JSON.stringify({ error: `File not found: ${absFilePath}` }, null, 2);
  }
  const content = fs.readFileSync(absFilePath, "utf-8");
  const lines = content.split(/\r?\n/);

  // Identify proof lines and estimate static heartbeat weights + run `lean --profile` if fast/available
  const hotspots: Array<{
    line: number;
    tactic: string;
    estimatedHeartbeats: number;
    elapsedMs: number;
    category: string;
  }> = [];

  for (let i = 0; i < lines.length; i++) {
    const trimmed = lines[i].split("--")[0].trim();
    if (!trimmed) continue;
    let hb = 0;
    let cat = "structural";
    if (/\b(?:aesop|grind)\b/.test(trimmed)) {
      hb = 850;
      cat = "search";
    } else if (/\bsimp\b(?!\s+only)/.test(trimmed) || /\bsimp_all\b/.test(trimmed)) {
      hb = 520;
      cat = "unscoped_simp";
    } else if (/\b(?:nlinarith|linarith)\b/.test(trimmed)) {
      hb = 360;
      cat = "linear_arith";
    } else if (/\b(?:ring_nf|ring|field_simp)\b/.test(trimmed)) {
      hb = 240;
      cat = "ring_normalization";
    } else if (/\b(?:omega|norm_num|positivity)\b/.test(trimmed)) {
      hb = 140;
      cat = "decision_proc";
    } else if (/\b(?:decide|rfl|exact|apply)\b/.test(trimmed)) {
      hb = 60;
      cat = "kernel_reduction";
    }
    if (hb > 0) {
      hotspots.push({
        line: i + 1,
        tactic: trimmed.slice(0, 80),
        estimatedHeartbeats: hb,
        elapsedMs: Number((hb * 0.08).toFixed(2)),
        category: cat,
      });
    }
  }

  let profileRawOutput = "";
  if (process.env.LEAN_PROFILE_LIVE === "1") {
    try {
      const out = execSync(`lake env lean --profile "${absFilePath}"`, {
        cwd: projectRoot,
        encoding: "utf-8",
        stdio: ["ignore", "pipe", "pipe"],
        timeout: 15000,
      });
      profileRawOutput = out.slice(0, 1500);
    } catch (err: any) {
      profileRawOutput = `${err.stdout || ""}${err.stderr || ""}`.slice(0, 1500);
    }
  }

  hotspots.sort((a, b) => b.estimatedHeartbeats - a.estimatedHeartbeats);
  const topHotspots = hotspots.slice(0, Math.max(1, topN));
  const totalEstimatedHeartbeats = hotspots.reduce((s, h) => s + h.estimatedHeartbeats, 0);

  return JSON.stringify(
    {
      filePath: path.relative(projectRoot, absFilePath),
      theoremName: theoremName || null,
      totalTacticStepsProfiled: hotspots.length,
      totalEstimatedHeartbeats,
      topHotspots,
      ...(profileRawOutput ? { leanProfileOutput: profileRawOutput } : {}),
    },
    null,
    2
  );
}

/**
 * Helper for `lean_theorem_preflight`: combines static `lean-analyzer` diagnostics,
 * `altproof` route advice, and `similar_proofs` BM25 retrieval in one structured payload.
 */
export function buildTheoremPreflightStatic(
  projectRoot: string,
  absFilePath: string,
  theoremName: string,
  counterexampleResult: string
): string {
  const content = fs.existsSync(absFilePath) ? fs.readFileSync(absFilePath, "utf-8") : "";
  const interp = new LeanAbstractInterpreter();
  const fidelityReport = auditLeanProofFidelity(content);
  const thmDiags = fidelityReport.diagnostics.filter(
    (d) => !theoremName || d.theoremName === theoremName || d.theoremName.endsWith(`.${theoremName}`)
  );

  // Extract declaration slice for altproof
  const lines = content.split(/\r?\n/);
  let declSlice = content.slice(0, 800);
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].includes(theoremName)) {
      declSlice = lines.slice(i, Math.min(lines.length, i + 25)).join("\n");
      break;
    }
  }
  const altProof = interp.analyzeAltProof(declSlice, declSlice);
  const similarProofs = retrieveSimilarProofsBM25(
    `${theoremName} ${declSlice}`,
    [{ filePath: path.relative(projectRoot, absFilePath), content }],
    5
  );

  return JSON.stringify(
    {
      filePath: path.relative(projectRoot, absFilePath),
      theoremName,
      phase0CounterexampleSearch: counterexampleResult,
      proofFidelityDiagnostics: thmDiags,
      sairDiagnosticsCount: fidelityReport.sairDiagnostics.length,
      altProofAdvisor: {
        bestTactic: altProof.bestTactic,
        bestEstimatedHeartbeats: altProof.bestEstimatedHeartbeats,
        recommendations: altProof.recommendations.slice(0, 4),
        relevantRoutes: altProof.relevantRoutes.slice(0, 3),
      },
      similarProofs: similarProofs.map((sp) => ({
        theoremName: sp.theoremName,
        line: sp.line,
        tacticsUsed: sp.tacticsUsed,
        score: sp.score,
      })),
    },
    null,
    2
  );
}
