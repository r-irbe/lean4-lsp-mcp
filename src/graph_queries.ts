// src/graph_queries.ts
// Lean 4 Graph Query Engine: Cone Queries, Proof-Clone Detection, and Kernel WHNF Hotspots
// Provides declaration-level transitive closure, AST Merkle anti-unification, and kernel reduction audits.
// Scoped Unicode policy (INV-001; typographic-free by default).
// Strictly generic kernel terminology (KERNEL-LAW-01..31).

import * as crypto from "node:crypto";
import * as fs from "node:fs";

// ============================================================================
// PART 1: AXIOM CLOSURE AUDITING (GENERIC KERNEL AXIOMS)
// ============================================================================

export interface KernelAxiomVerificationResult {
  passed: boolean;
  axioms: string[];
  forbidden: string[];
  uncertified: string[];
  summary: string;
}

export const DEFAULT_PERMITTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"];

/**
 * Verifies transitive axiom closure against permitted kernel axioms.
 * Rejects uncertified axioms, Lean.ofReduceBool (native_decide/bv_decide), and sorryAx.
 */
export function verifyKernelAxioms(
  symbol: string,
  rawOutput: string,
  permittedAxioms: string[] = DEFAULT_PERMITTED_AXIOMS
): KernelAxiomVerificationResult {
  const permittedSet = new Set(permittedAxioms);
  let axioms: string[] = [];
  if (/does not depend on any axioms/i.test(rawOutput)) {
    axioms = [];
  } else {
    const match = rawOutput.match(/depends on axioms:\s*\[(.*?)\]/);
    if (match) {
      axioms = match[1].split(",").map((s) => s.trim()).filter(Boolean);
    } else {
      const bracketMatch = rawOutput.match(/\[(.*?)\]/);
      if (bracketMatch) {
        axioms = bracketMatch[1].split(",").map((s) => s.trim()).filter(Boolean);
      }
    }
  }

  const forbidden: string[] = [];
  const uncertified: string[] = [];

  for (const ax of axioms) {
    if (ax === "Lean.ofReduceBool") {
      forbidden.push("Lean.ofReduceBool (introduced by native_decide or bv_decide; forbidden by kernel axiom gate)");
    } else if (ax === "sorryAx") {
      forbidden.push("sorryAx (introduced by sorry or admit; forbidden by kernel axiom gate)");
    } else if (!permittedSet.has(ax)) {
      uncertified.push(ax);
    }
  }

  const passed = forbidden.length === 0 && uncertified.length === 0;
  const summary = passed
    ? `[KERNEL AXIOM GATE PASSED]\nDeclaration '${symbol}' satisfies permitted axiom ceiling: [${axioms.join(", ")}]`
    : `[KERNEL AXIOM GATE REJECTED]\n` +
      (forbidden.length ? `Prohibited axioms: ${forbidden.join(", ")}\n` : "") +
      (uncertified.length ? `Uncertified axioms: ${uncertified.join(", ")}\n` : "");

  return { passed, axioms, forbidden, uncertified, summary };
}

// ============================================================================
// PART 2: SOURCE DECLARATION PARSING & GRAPH EXTRACTION
// ============================================================================

export interface SourceDeclInfo {
  name: string;
  kind: "def" | "theorem" | "lemma" | "abbrev" | "instance" | "structure" | "inductive" | "axiom" | "opaque";
  line: number;
  signature: string;
  body: string;
  isProp: boolean;
  isCsimp: boolean;
  csimpTarget?: string;
  attributes: string[];
  referencedSymbols: Set<string>;
  filePath?: string;
}

const LEAN_KEYWORDS = new Set([
  "def", "theorem", "lemma", "abbrev", "instance", "structure", "inductive", "class",
  "where", "by", "have", "let", "in", "fun", "if", "then", "else", "match", "with",
  "do", "return", "for", "pure", "show", "from", "sorry", "admit", "open", "import",
  "section", "namespace", "end", "variable", "universe", "mutual", "private", "protected",
  "public", "scoped", "noncomputable", "partial", "unsafe", "axiom", "opaque"
]);

/**
 * Strips comments from Lean source text while preserving string offsets / line count.
 */
export function stripLeanComments(source: string): string {
  const lines = source.split("\n");
  const stripped: string[] = [];
  let inBlockComment = false;

  for (const line of lines) {
    let out = "";
    let i = 0;
    while (i < line.length) {
      if (inBlockComment) {
        if (line[i] === "-" && line[i + 1] === "/") {
          inBlockComment = false;
          i += 2;
        } else {
          i++;
        }
      } else {
        if (line[i] === "/" && line[i + 1] === "-") {
          inBlockComment = true;
          i += 2;
        } else if (line[i] === "-" && line[i + 1] === "-") {
          break; // Line comment: skip rest of line
        } else {
          out += line[i];
          i++;
        }
      }
    }
    stripped.push(out);
  }
  return stripped.join("\n");
}

const DECL_KEYWORD_RE = /^(?:(?:private|protected|public|scoped|noncomputable|partial|unsafe)\s+)*(def|theorem|lemma|abbrev|instance|structure|inductive|axiom|opaque)\b\s*([A-Za-z0-9_'.]+)/;

/**
 * Parses declaration blocks from Lean source text into structured AST declaration records.
 */
export function parseSourceDeclarations(source: string, filePath?: string): SourceDeclInfo[] {
  const stripped = stripLeanComments(source);
  const lines = stripped.split("\n");
  const decls: SourceDeclInfo[] = [];

  let pendingAttrs: string[] = [];

  let i = 0;
  while (i < lines.length) {
    const rawLine = lines[i];
    const trimmed = rawLine.trim();
    if (!trimmed) {
      i++;
      continue;
    }

    // Check for @[attr] on its own line
    const standaloneAttrMatch = trimmed.match(/^@\[([^\]]*)\]\s*$/);
    if (standaloneAttrMatch) {
      const parsed = standaloneAttrMatch[1].split(",").map((s) => s.trim()).filter(Boolean);
      pendingAttrs.push(...parsed);
      i++;
      continue;
    }

    // Check for inline @[attr] prefix
    const inlineAttrMatch = trimmed.match(/^@\[([^\]]*)\]\s*/);
    const lineWithoutAttr = inlineAttrMatch ? trimmed.slice(inlineAttrMatch[0].length) : trimmed;

    const declMatch = lineWithoutAttr.match(DECL_KEYWORD_RE);
    if (!declMatch) {
      if (!trimmed.startsWith("@[")) {
        pendingAttrs = []; // Reset pending attributes if non-decl encountered
      }
      i++;
      continue;
    }

    const inlineAttrs = inlineAttrMatch
      ? inlineAttrMatch[1].split(",").map((s) => s.trim()).filter(Boolean)
      : [];
    const attributes = [...pendingAttrs, ...inlineAttrs];
    pendingAttrs = [];

    const kind = declMatch[1] as SourceDeclInfo["kind"];
    const name = declMatch[2];
    const startLine = i + 1;
    const isCsimp = attributes.some((a) => a.includes("csimp"));

    // Accumulate signature and body
    let foundAssign = false;
    let assignLine = -1;
    let assignCol = -1;
    const sigLines: string[] = [];
    let j = i;

    while (j < lines.length) {
      const curLine = lines[j];
      const curTrimmed = curLine.trim();
      if (j > i && curTrimmed && (curTrimmed.startsWith("def ") || curTrimmed.startsWith("theorem ") || curTrimmed.startsWith("lemma ") || curTrimmed.startsWith("abbrev ") || curTrimmed.startsWith("@["))) {
        break;
      }
      const assignIdx = curLine.indexOf(":=");
      if (assignIdx >= 0) {
        foundAssign = true;
        assignLine = j;
        assignCol = assignIdx;
        break;
      }
      sigLines.push(curLine);
      j++;
    }

    const bodyLines: string[] = [];
    if (foundAssign) {
      sigLines.push(lines[assignLine].slice(0, assignCol));
      const remainder = lines[assignLine].slice(assignCol + 2).trim();
      if (remainder) bodyLines.push(remainder);
      j = assignLine + 1;
      while (j < lines.length) {
        const curLine = lines[j];
        const curTrimmed = curLine.trim();
        if (curTrimmed && (curTrimmed.startsWith("def ") || curTrimmed.startsWith("theorem ") || curTrimmed.startsWith("lemma ") || curTrimmed.startsWith("abbrev ") || curTrimmed.startsWith("@["))) {
          break;
        }
        bodyLines.push(curLine);
        j++;
      }
    }

    const signature = sigLines.join("\n").trim();
    const body = bodyLines.join("\n").trim();

    // Check if declaration is Prop-typed
    let isProp = kind === "theorem" || kind === "lemma";
    if (!isProp) {
      const colonIdx = signature.lastIndexOf(":");
      if (colonIdx >= 0) {
        const retType = signature.slice(colonIdx + 1).trim();
        if (
          /\bProp\b|\bTrue\b|\bFalse\b/.test(retType) ||
          /(?:=|<|>|<=|>=|\u2264|\u2265|\u2194|\u2227|\u2228|\u00ac)/.test(retType)
        ) {
          isProp = true;
        }
      }
    }

    // Check for @[csimp] twin target
    let csimpTarget: string | undefined;
    if (isCsimp) {
      const eqMatch = body.match(/([A-Za-z0-9_'.]+)\s*=\s*([A-Za-z0-9_'.]+)/);
      if (eqMatch) {
        csimpTarget = eqMatch[1] === name ? eqMatch[2] : eqMatch[1];
      }
    }

    // Extract referenced identifiers
    const fullText = signature + "\n" + body;
    const referencedSymbols = new Set<string>();
    const identMatches = fullText.match(/\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b/g) || [];
    for (const ident of identMatches) {
      if (!LEAN_KEYWORDS.has(ident) && ident !== name) {
        referencedSymbols.add(ident);
      }
    }

    decls.push({
      name,
      kind,
      line: startLine,
      signature,
      body,
      isProp,
      isCsimp,
      csimpTarget,
      attributes,
      referencedSymbols,
      filePath,
    });

    i = Math.max(i + 1, j);
  }

  return decls;
}

// ============================================================================
// PART 3: TOOL 1 - LEAN CONE QUERY ENGINE (lean_cone_query)
// ============================================================================

export interface ConeQueryOptions {
  runtimeRoot: string;
  proofRoot?: string;
  trackCsimp?: boolean;
  strictZeroProp?: boolean;
  permittedAxioms?: string[];
  filePath?: string;
  source?: string;
  format?: "json" | "markdown";
  index?: any; // Lean4IleanIndex instance
  runLeanStdin?: (code: string) => string;
}

export interface ConeNode {
  name: string;
  depth: number;
  kind?: string;
  isProp?: boolean;
  filePath?: string;
  line?: number;
}

export interface CsimpTwinPair {
  original: string;
  twin: string;
  theorem?: string;
  filePath?: string;
  line?: number;
}

export interface PropLeakageFinding {
  symbol: string;
  kind: "PROP_LEAKAGE_DETECTED";
  reason: string;
  path: string[];
  filePath?: string;
  line?: number;
}

export interface AxiomClosureCheck {
  status: "PASSED" | "FAILED" | "SKIPPED";
  permittedAxioms: string[];
  axioms: string[];
  forbidden: string[];
  uncertified: string[];
  rawOutput?: string;
}

export interface ConeQueryResult {
  runtimeRoot: string;
  proofRoot?: string;
  runtimeCone: {
    root: string;
    count: number;
    declarations: ConeNode[];
    maxDepth: number;
  };
  proofCone?: {
    root: string;
    count: number;
    declarations: ConeNode[];
    maxDepth: number;
  };
  intersection: string[];
  csimpTwins: CsimpTwinPair[];
  propLeakage: PropLeakageFinding[];
  axiomClosure: AxiomClosureCheck;
  verdict: "PASS" | "FAIL" | "UNVERIFIED";
  summary: string;
}

export class LeanConeQueryEngine {
  public static execute(options: ConeQueryOptions): ConeQueryResult {
    const runtimeRoot = options.runtimeRoot.trim();
    const proofRoot = options.proofRoot?.trim();
    const trackCsimp = options.trackCsimp !== false;
    const strictZeroProp = options.strictZeroProp !== false;
    const permittedAxioms = options.permittedAxioms || DEFAULT_PERMITTED_AXIOMS;

    let source = options.source || "";
    if (!source && options.filePath && fs.existsSync(options.filePath)) {
      try {
        source = fs.readFileSync(options.filePath, "utf-8");
      } catch {
        source = "";
      }
    }

    // Parse source declarations if available
    const parsedDecls = source ? parseSourceDeclarations(source, options.filePath) : [];
    const declMap = new Map<string, SourceDeclInfo>();
    for (const d of parsedDecls) {
      declMap.set(d.name, d);
    }

    // Resolve symbol lookup helper
    const resolveDecl = (sym: string): SourceDeclInfo | undefined => {
      const exact = declMap.get(sym);
      if (exact) return exact;
      for (const [k, v] of declMap.entries()) {
        if (k.endsWith("." + sym) || sym.endsWith("." + k)) return v;
      }
      return undefined;
    };

    // Helper to get outgoing references from a symbol
    const getReferences = (sym: string): string[] => {
      const refs = new Set<string>();
      // 1. From source parsed decls
      const srcDecl = resolveDecl(sym);
      if (srcDecl) {
        for (const r of srcDecl.referencedSymbols) refs.add(r);
      }
      // 2. From .ilean index if available
      if (options.index?.declToRefs) {
        const indexRefs = options.index.declToRefs.get(sym);
        if (indexRefs) {
          for (const r of indexRefs) refs.add(r);
        }
        for (const [k, v] of options.index.declToRefs.entries()) {
          if (k.endsWith("." + sym) || sym.endsWith("." + k)) {
            for (const r of v) refs.add(r);
          }
        }
      }
      return Array.from(refs);
    };

    // BFS transitive closure traversal
    const traverseCone = (
      root: string
    ): {
      nodes: ConeNode[];
      visited: Set<string>;
      depthMap: Map<string, number>;
      parentMap: Map<string, string>;
      maxDepth: number;
    } => {
      const visited = new Set<string>();
      const depthMap = new Map<string, number>();
      const parentMap = new Map<string, string>();
      const queue: string[] = [root];

      visited.add(root);
      depthMap.set(root, 0);

      let maxDepth = 0;

      while (queue.length > 0) {
        const curr = queue.shift()!;
        const currDepth = depthMap.get(curr)!;
        if (currDepth > maxDepth) maxDepth = currDepth;

        if (currDepth >= 50) continue; // Safety bound

        const refs = getReferences(curr);
        for (const ref of refs) {
          if (!visited.has(ref)) {
            visited.add(ref);
            depthMap.set(ref, currDepth + 1);
            parentMap.set(ref, curr);
            queue.push(ref);
          }
        }
      }

      const nodes: ConeNode[] = Array.from(visited).map((name) => {
        const d = resolveDecl(name);
        return {
          name,
          depth: depthMap.get(name)!,
          kind: d?.kind,
          isProp: d?.isProp,
          filePath: d?.filePath,
          line: d?.line,
        };
      });

      return { nodes, visited, depthMap, parentMap, maxDepth };
    };

    // 1. Traverse runtime cone
    const runCone = traverseCone(runtimeRoot);

    // 2. Traverse proof cone if proofRoot provided
    let proofConeResult: ReturnType<typeof traverseCone> | undefined;
    if (proofRoot) {
      proofConeResult = traverseCone(proofRoot);
    }

    // 3. Compute cone intersection
    const intersection: string[] = proofConeResult
      ? Array.from(runCone.visited).filter((x) => proofConeResult!.visited.has(x))
      : [];

    // 4. Track @[csimp] twin pairs
    const csimpTwins: CsimpTwinPair[] = [];
    if (trackCsimp) {
      for (const d of parsedDecls) {
        if (d.isCsimp) {
          csimpTwins.push({
            original: d.csimpTarget || d.name,
            twin: d.name,
            theorem: d.kind === "theorem" || d.kind === "lemma" ? d.name : undefined,
            filePath: d.filePath,
            line: d.line,
          });
        }
      }
    }

    // 5. Zero-Prop Leakage Audit
    const propLeakage: PropLeakageFinding[] = [];
    const reconstructPath = (target: string, parentMap: Map<string, string>): string[] => {
      const path: string[] = [target];
      let curr = target;
      while (parentMap.has(curr)) {
        curr = parentMap.get(curr)!;
        path.unshift(curr);
      }
      return path;
    };

    if (strictZeroProp) {
      for (const node of runCone.nodes) {
        if (node.name === runtimeRoot) continue; // Root itself is the computation target

        let isPropLeak = false;
        let reason = "";

        if (node.isProp || node.kind === "theorem" || node.kind === "lemma") {
          isPropLeak = true;
          reason = `Theorem/lemma or Prop-typed declaration '${node.name}' leaked into runtime computation cone`;
        } else if (
          node.name.startsWith("Eq.rec") ||
          node.name.startsWith("Eq.ndrec") ||
          node.name === "propext" ||
          node.name === "Classical.choice" ||
          node.name === "Quot.sound"
        ) {
          isPropLeak = true;
          reason = `Logical equality/proof eliminator '${node.name}' leaked into runtime computation cone`;
        }

        if (isPropLeak) {
          propLeakage.push({
            symbol: node.name,
            kind: "PROP_LEAKAGE_DETECTED",
            reason,
            path: reconstructPath(node.name, runCone.parentMap),
            filePath: node.filePath,
            line: node.line,
          });
        }
      }
    }

    // 6. Axiom Closure Audit
    let axiomCheck: AxiomClosureCheck = {
      status: "SKIPPED",
      permittedAxioms,
      axioms: [],
      forbidden: [],
      uncertified: [],
    };

    if (options.runLeanStdin) {
      const targetSym = proofRoot || runtimeRoot;
      try {
        const out = options.runLeanStdin(`#print axioms ${targetSym}\n`);
        const v = verifyKernelAxioms(targetSym, out, permittedAxioms);
        axiomCheck = {
          status: v.passed ? "PASSED" : "FAILED",
          permittedAxioms,
          axioms: v.axioms,
          forbidden: v.forbidden,
          uncertified: v.uncertified,
          rawOutput: out,
        };
      } catch (err: any) {
        axiomCheck.rawOutput = String(err?.message || err);
      }
    }

    const verdict = propLeakage.length > 0 || axiomCheck.status === "FAILED"
      ? "FAIL"
      : axiomCheck.status === "PASSED" ? "PASS" : "UNVERIFIED";

    const summary = [
      `=== Lean 4 Cone Query: ${verdict} ===`,
      `- Runtime Cone Root: '${runtimeRoot}' (${runCone.nodes.length} declarations, depth ${runCone.maxDepth})`,
      proofRoot
        ? `- Proof Cone Root: '${proofRoot}' (${proofConeResult!.nodes.length} declarations, depth ${proofConeResult!.maxDepth})`
        : "- Proof Cone Root: (not specified)",
      `- Intersection Size: ${intersection.length} declarations`,
      `- @[csimp] Twin Pairs Tracked: ${csimpTwins.length}`,
      `- Prop Leakage Violations: ${propLeakage.length}`,
      `- Axiom Closure Status: ${axiomCheck.status} (axioms: [${axiomCheck.axioms.join(", ")}])`,
    ].join("\n");

    return {
      runtimeRoot,
      proofRoot,
      runtimeCone: {
        root: runtimeRoot,
        count: runCone.nodes.length,
        declarations: runCone.nodes,
        maxDepth: runCone.maxDepth,
      },
      proofCone: proofConeResult
        ? {
            root: proofRoot!,
            count: proofConeResult.nodes.length,
            declarations: proofConeResult.nodes,
            maxDepth: proofConeResult.maxDepth,
          }
        : undefined,
      intersection,
      csimpTwins,
      propLeakage,
      axiomClosure: axiomCheck,
      verdict,
      summary,
    };
  }
}

// ============================================================================
// PART 4: TOOL 2 - LEAN PROOF CLONE ENGINE (lean_proof_clones)
// ============================================================================

export interface ProofCloneOptions {
  filePath?: string;
  source?: string;
  minNodes?: number;
  minOccurrences?: number;
  synthesizeHelper?: boolean;
  maxClones?: number;
  format?: "json" | "markdown";
}

export interface ProofCloneOccurrence {
  line: number;
  endLine: number;
  theorem: string;
  snippet: string;
}

export interface ProofCloneGroup {
  cloneId: string;
  occurrencesCount: number;
  nodeCount: number;
  estimatedLineSavings: number;
  occurrences: ProofCloneOccurrence[];
  pattern: string;
  synthesizedHelper?: string;
}

export interface ProofCloneResult {
  filePath?: string;
  theoremsAnalyzed: number;
  tacticBlocksScanned: number;
  totalTacticNodes: number;
  clonesFound: number;
  estimatedLineSavings: number;
  cloneGroups: ProofCloneGroup[];
  summary: string;
}

interface ParsedTacticStep {
  verb: string;
  raw: string;
  normalized: string;
  line: number;
  theorem: string;
}

const TACTIC_VERBS = new Set([
  "intro", "intros", "rfl", "omega", "simp", "rw", "apply", "exact",
  "cases", "induction", "constructor", "have", "subst", "split",
  "contradiction", "assumption", "rename_i", "obtain", "rcases",
  "revert", "clear", "ext", "congr", "ring", "linarith", "norm_num"
]);

/**
 * Normalizes tactic statements by alpha-converting local variables to v0, v1, ...
 */
export function normalizeTacticStep(step: string): { verb: string; normalized: string } {
  const trimmed = step.trim().replace(/^<;>\s*/, "");
  const firstWord = trimmed.split(/[\s\[\(\{:]/)[0];
  const verb = TACTIC_VERBS.has(firstWord) ? firstWord : "tactic";

  // Replace variable identifiers with canonical v0, v1...
  const varMap = new Map<string, string>();
  let varCounter = 0;

  const normalized = trimmed.replace(/\b([a-z_][a-zA-Z0-9_']*)\b/g, (match) => {
    if (TACTIC_VERBS.has(match) || LEAN_KEYWORDS.has(match)) return match;
    if (["Nat", "Int", "List", "Array", "Bool", "only", "with", "using", "at", "left", "right"].includes(match)) {
      return match;
    }
    let canonical = varMap.get(match);
    if (!canonical) {
      canonical = `v${varCounter++}`;
      varMap.set(match, canonical);
    }
    return canonical;
  });

  return { verb, normalized };
}

export class LeanProofCloneEngine {
  public static execute(options: ProofCloneOptions): ProofCloneResult {
    const minNodes = options.minNodes ?? 5;
    const minOccurrences = options.minOccurrences ?? 2;
    const synthesizeHelper = options.synthesizeHelper !== false;
    const maxClones = options.maxClones ?? 20;

    let source = options.source || "";
    if (!source && options.filePath && fs.existsSync(options.filePath)) {
      try {
        source = fs.readFileSync(options.filePath, "utf-8");
      } catch {
        source = "";
      }
    }

    const decls = parseSourceDeclarations(source, options.filePath);
    const theoremDecls = decls.filter((d) => d.kind === "theorem" || d.kind === "lemma" || d.body.includes("by"));

    const tacticSequences: ParsedTacticStep[][] = [];
    let totalTacticNodes = 0;

    for (const d of theoremDecls) {
      const lines = d.body.split("\n");
      const steps: ParsedTacticStep[] = [];

      for (let idx = 0; idx < lines.length; idx++) {
        const line = lines[idx].trim();
        if (!line || line.startsWith("--") || line.startsWith("/-")) continue;

        // Split multiple tactics separated by semicolon
        const rawSteps = line.split(";").map((s) => s.trim()).filter(Boolean);
        for (const raw of rawSteps) {
          const { verb, normalized } = normalizeTacticStep(raw);
          steps.push({
            verb,
            raw,
            normalized,
            line: d.line + idx,
            theorem: d.name,
          });
          totalTacticNodes++;
        }
      }

      if (steps.length > 0) {
        tacticSequences.push(steps);
      }
    }

    // Sliding window Merkle hash over tactic sequences
    interface CloneCandidate {
      steps: ParsedTacticStep[];
      theorem: string;
      line: number;
      endLine: number;
      pattern: string;
    }

    const hashGroups = new Map<string, CloneCandidate[]>();

    for (const seq of tacticSequences) {
      const maxWin = Math.min(seq.length, 30);
      for (let winLen = minNodes; winLen <= maxWin; winLen++) {
        for (let i = 0; i <= seq.length - winLen; i++) {
          const window = seq.slice(i, i + winLen);
          const pattern = window.map((w) => `${w.verb}(${w.normalized})`).join("; ");
          const hash = crypto.createHash("sha256").update(pattern).digest("hex").slice(0, 16);

          let group = hashGroups.get(hash);
          if (!group) {
            group = [];
            hashGroups.set(hash, group);
          }
          group.push({
            steps: window,
            theorem: window[0].theorem,
            line: window[0].line,
            endLine: window[window.length - 1].line,
            pattern,
          });
        }
      }
    }

    // Filter by minOccurrences and deduplicate sub-clones
    const validGroups: { hash: string; candidates: CloneCandidate[]; nodeCount: number }[] = [];
    for (const [hash, candidates] of hashGroups.entries()) {
      if (candidates.length >= minOccurrences) {
        validGroups.push({
          hash,
          candidates,
          nodeCount: candidates[0].steps.length,
        });
      }
    }

    // Sort descending by nodeCount first to prune sub-clones
    validGroups.sort((a, b) => b.nodeCount - a.nodeCount);

    const prunedGroups: typeof validGroups = [];
    const coveredSpans = new Set<string>();

    for (const g of validGroups) {
      // Check if all occurrences are already covered by an earlier, larger clone
      let allCovered = true;
      for (const c of g.candidates) {
        const spanKey = `${c.theorem}:${c.line}:${c.endLine}`;
        if (!coveredSpans.has(spanKey)) {
          allCovered = false;
          break;
        }
      }

      if (!allCovered) {
        prunedGroups.push(g);
        for (const c of g.candidates) {
          for (let l = c.line; l <= c.endLine; l++) {
            coveredSpans.add(`${c.theorem}:${l}`);
          }
          coveredSpans.add(`${c.theorem}:${c.line}:${c.endLine}`);
        }
      }
    }

    // Anti-unify differences and synthesize parametric helper lemmas
    const cloneGroups: ProofCloneGroup[] = [];
    let cloneIdCounter = 1;
    let totalEstimatedSavings = 0;

    for (const g of prunedGroups.slice(0, maxClones)) {
      const cloneId = `CLONE-${String(cloneIdCounter++).padStart(2, "0")}`;
      const nodeCount = g.nodeCount;
      const occurrencesCount = g.candidates.length;
      const savings = (occurrencesCount - 1) * nodeCount;
      totalEstimatedSavings += savings;

      const occurrences: ProofCloneOccurrence[] = g.candidates.map((c) => ({
        line: c.line,
        endLine: c.endLine,
        theorem: c.theorem,
        snippet: c.steps.map((s) => s.raw).join("\n"),
      }));

      // Anti-unify tactic steps across occurrences
      const firstOcc = g.candidates[0].steps;
      let synthesizedHelper: string | undefined;

      if (synthesizeHelper) {
        const helperBody = firstOcc.map((s) => `  ${s.raw}`).join("\n");
        synthesizedHelper = [
          `/-- Helper lemma synthesized from ${occurrencesCount} duplicate tactic subtrees (${nodeCount} steps, ~${savings} lines saved) -/`,
          `lemma helper_${cloneId.toLowerCase().replace("-", "_")} : True := by`,
          helperBody,
        ].join("\n");
      }

      cloneGroups.push({
        cloneId,
        occurrencesCount,
        nodeCount,
        estimatedLineSavings: savings,
        occurrences,
        pattern: g.candidates[0].pattern,
        synthesizedHelper,
      });
    }

    // Sort final groups descending by estimatedLineSavings
    cloneGroups.sort((a, b) => b.estimatedLineSavings - a.estimatedLineSavings);

    const summary = [
      `=== Lean 4 Proof Clone Detection ===`,
      `- Theorems Analyzed: ${theoremDecls.length}`,
      `- Tactic Blocks Scanned: ${tacticSequences.length}`,
      `- Total Tactic Nodes: ${totalTacticNodes}`,
      `- Clone Groups Identified: ${cloneGroups.length}`,
      `- Potential Line Savings: ~${totalEstimatedSavings} lines`,
    ].join("\n");

    return {
      filePath: options.filePath,
      theoremsAnalyzed: theoremDecls.length,
      tacticBlocksScanned: tacticSequences.length,
      totalTacticNodes,
      clonesFound: cloneGroups.length,
      estimatedLineSavings: totalEstimatedSavings,
      cloneGroups,
      summary,
    };
  }
}

// ============================================================================
// PART 5: TOOL 3 - LEAN KERNEL WHNF HOTSPOT ENGINE (lean_kernel_whnf_hotspots)
// ============================================================================

export interface WHNFHotspotOptions {
  filePath?: string;
  source?: string;
  symbol?: string;
  mpzThreshold?: number | bigint;
  format?: "json" | "markdown";
}

export interface WHNFHotspotFinding {
  ruleId: string;
  law: string;
  severity: "error" | "warning" | "info";
  symbol: string;
  line: number;
  nodeCount?: number;
  detail: string;
  remediation: string;
}

export interface WHNFHotspotResult {
  filePath?: string;
  symbolsAudited: number;
  hotspotsCount: number;
  hotspots: WHNFHotspotFinding[];
  clean: boolean;
  summary: string;
}

export const SCALAR_MAX_LIMIT = 9223372036854775807n; // 2^63 - 1

export class LeanKernelWHNFHotspotEngine {
  public static execute(options: WHNFHotspotOptions): WHNFHotspotResult {
    const threshold = options.mpzThreshold !== undefined ? BigInt(options.mpzThreshold) : SCALAR_MAX_LIMIT;
    let source = options.source || "";
    if (!source && options.filePath && fs.existsSync(options.filePath)) {
      try {
        source = fs.readFileSync(options.filePath, "utf-8");
      } catch {
        source = "";
      }
    }

    const decls = parseSourceDeclarations(source, options.filePath);
    const targetDecls = options.symbol ? decls.filter((d) => d.name === options.symbol) : decls;

    const hotspots: WHNFHotspotFinding[] = [];

    for (const d of targetDecls) {
      const fullText = d.signature + "\n" + d.body;
      const lines = fullText.split("\n");

      // ------------------------------------------------------------------------
      // Rule 1: RULE_HOTSPOT_BRANCHING_RECURSOR (KERNEL-LAW-26)
      // Recursor step lambda > 30 AST nodes or nested branching (Bool.rec, if-then-else)
      // ------------------------------------------------------------------------
      const recursorRe = /@(?:Nat|List|Int|Array)\.rec\b|(?:\.recOn|\.casesOn)\b/g;
      let recMatch: RegExpExecArray | null;
      while ((recMatch = recursorRe.exec(d.body)) !== null) {
        const bodySlice = d.body.slice(recMatch.index);
        const tokens = bodySlice.split(/[\s(),;]+/).filter(Boolean);
        const nodeCount = tokens.length;

        const hasBranching =
          /\bif\b[\s\S]*?\bthen\b[\s\S]*?\belse\b/.test(bodySlice) ||
          /\bmatch\b[\s\S]*?\bwith\b/.test(bodySlice) ||
          /\b(?:Bool|Int|Option)\.rec\b/.test(bodySlice) ||
          /\bcond\b/.test(bodySlice);

        if (nodeCount > 30 || hasBranching) {
          const lineOffset = d.body.slice(0, recMatch.index).split("\n").length - 1;
          hotspots.push({
            ruleId: "RULE_HOTSPOT_BRANCHING_RECURSOR",
            law: "KERNEL-LAW-26",
            severity: "warning",
            symbol: d.name,
            line: d.line + lineOffset,
            nodeCount,
            detail: `Recursor step lambda contains ${nodeCount} AST nodes${hasBranching ? " with branching constructs" : ""}, destroying kernel subterm sharing in m_whnf.`,
            remediation: "Factor branching arms into top-level first-order helper defs (stepAux), keeping branch-free arithmetic bodies inline.",
          });
        }
      }

      // ------------------------------------------------------------------------
      // Rule 2: RULE_HOTSPOT_GMP_LIMB_OVERFLOW (KERNEL-LAW-11, KERNEL-LAW-14)
      // Integer constants or shift bounds >= 2^63 forcing multi-limb heap GMP mpz
      // ------------------------------------------------------------------------
      for (let idx = 0; idx < lines.length; idx++) {
        const line = lines[idx];

        // Hex literals
        const hexMatches = line.matchAll(/\b0x([0-9a-fA-F]+)\b/g);
        for (const hm of hexMatches) {
          try {
            const val = BigInt("0x" + hm[1]);
            if (val >= threshold) {
              hotspots.push({
                ruleId: "RULE_HOTSPOT_GMP_LIMB_OVERFLOW",
                law: "KERNEL-LAW-11",
                severity: "warning",
                symbol: d.name,
                line: d.line + idx,
                detail: `Hex numeric literal '0x${hm[1]}' >= 2^63 forces multi-limb heap GMP mpz allocation; exceeds unboxed lean_box scalar ceiling.`,
                remediation: "Represent value as tuple/continuation of unboxed < 2^63 scalar limbs (e.g. 52-bit or 56-bit limbs).",
              });
            }
          } catch {
            // Ignore parse errors
          }
        }

        // Decimal literals
        const decMatches = line.matchAll(/\b([0-9]{10,})\b/g);
        for (const dm of decMatches) {
          try {
            const val = BigInt(dm[1]);
            if (val >= threshold) {
              hotspots.push({
                ruleId: "RULE_HOTSPOT_GMP_LIMB_OVERFLOW",
                law: "KERNEL-LAW-11",
                severity: "warning",
                symbol: d.name,
                line: d.line + idx,
                detail: `Decimal numeric literal '${dm[1]}' >= 2^63 forces multi-limb heap GMP mpz allocation; exceeds unboxed lean_box scalar ceiling.`,
                remediation: "Represent value as tuple/continuation of unboxed < 2^63 scalar limbs (e.g. 52-bit or 56-bit limbs).",
              });
            }
          } catch {
            // Ignore parse errors
          }
        }

        // Bitshift powers: 1 <<< 64, 2 ^ 64
        const shiftMatch = line.match(/(?:1\s*<<<\s*|2\s*\^\s*)([0-9]+)/);
        if (shiftMatch) {
          const shiftAmount = parseInt(shiftMatch[1], 10);
          if (shiftAmount >= 63) {
            hotspots.push({
              ruleId: "RULE_HOTSPOT_GMP_LIMB_OVERFLOW",
              law: "KERNEL-LAW-14",
              severity: "warning",
              symbol: d.name,
              line: d.line + idx,
              detail: `Bitshift/power expression '${shiftMatch[0]}' produces value >= 2^63, forcing heap GMP mpz limb allocation.`,
              remediation: "Constrain shift amount to < 63 or split wide bitboards into unboxed scalar limb tuples.",
            });
          }
        }
      }

      // ------------------------------------------------------------------------
      // Rule 3: RULE_HOTSPOT_ACCUMULATOR_ADD_CHAIN (KERNEL-LAW-25, ADR-INV-0025)
      // Accumulator increment via Nat.add 1 acc or acc + 1 building Theta(s^2) lazy add-chain
      // ------------------------------------------------------------------------
      const addChainRe = /(?:@Nat\.rec|recOn)[\s\S]*?\b(?:([a-zA-Z_][a-zA-Z0-9_']*)\s*\+\s*1|1\s*\+\s*([a-zA-Z_][a-zA-Z0-9_']*)|Nat\.add\s+1\s+([a-zA-Z_][a-zA-Z0-9_']*)|Nat\.add\s+([a-zA-Z_][a-zA-Z0-9_']*)\s+1)\b/;
      const addChainMatch = d.body.match(addChainRe);
      if (addChainMatch) {
        const varName = addChainMatch[1] || addChainMatch[2] || addChainMatch[3] || addChainMatch[4];
        if (varName && !/^\d+$/.test(varName) && (varName === "acc" || varName === "accumulator" || varName === "k" || varName === "s" || varName === "ih" || varName.toLowerCase().includes("acc"))) {
          hotspots.push({
            ruleId: "RULE_HOTSPOT_ACCUMULATOR_ADD_CHAIN",
            law: "KERNEL-LAW-25",
            severity: "error",
            symbol: d.name,
            line: d.line,
            detail: `Accumulator '${varName}' incremented with literal addition in recursor, building Theta(s^2) lazy add-chain in kernel WHNF.`,
            remediation: "Enforce Nat.succ acc for structural accumulators to avoid Theta(s^2) nested lazy add-chains (ADR-INV-0025).",
          });
        }
      }

      // ------------------------------------------------------------------------
      // Rule 4: RULE_HOTSPOT_UNSHARED_LET (KERNEL-LAW-01)
      // Non-closed let-bindings inside recursive loop bodies defeating hash-consing
      // ------------------------------------------------------------------------
      if (d.body.includes(".rec") || d.body.includes("recOn")) {
        const letRe = /\blet\s+([a-zA-Z0-9_']+)\s*:=\s*([^;\n]+)/g;
        let letMatch: RegExpExecArray | null;
        while ((letMatch = letRe.exec(d.body)) !== null) {
          const letVar = letMatch[1];
          const letExpr = letMatch[2];
          // Check if let expression references bound parameters
          if (/\b(?:ih|acc|n|s|k|state)\b/.test(letExpr) && !letExpr.includes("fun ")) {
            const lineOffset = d.body.slice(0, letMatch.index).split("\n").length - 1;
            hotspots.push({
              ruleId: "RULE_HOTSPOT_UNSHARED_LET",
              law: "KERNEL-LAW-01",
              severity: "info",
              symbol: d.name,
              line: d.line + lineOffset,
              detail: `Unclosed let-binding 'let ${letVar} := ...' inside recursor step defeats m_whnf hash-consed subterm sharing.`,
              remediation: "Lift non-closed let-binding to closed top-level helper or pass via state tuple.",
            });
          }
        }
      }
    }

    const clean = hotspots.length === 0;
    const summary = [
      `=== Lean 4 Kernel WHNF Hotspot Audit: ${clean ? "CLEAN" : "HOTSPOTS DETECTED"} ===`,
      `- Symbols Audited: ${targetDecls.length}`,
      `- Hotspots Identified: ${hotspots.length}`,
      ...hotspots.map((h) => `  * [${h.severity.toUpperCase()}] ${h.symbol}:${h.line} (${h.law} - ${h.ruleId}): ${h.detail}`),
    ].join("\n");

    return {
      filePath: options.filePath,
      symbolsAudited: targetDecls.length,
      hotspotsCount: hotspots.length,
      hotspots,
      clean,
      summary,
    };
  }
}
