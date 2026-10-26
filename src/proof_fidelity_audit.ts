// src/proof_fidelity_audit.ts
// Automated specification & vacuity fidelity audit for Lean 4 source files.
// Detects all 7 structural defect classes:
//   1. HYPOTHESIS_ECHO
//   2. REFLEXIVE_TAUTOLOGY
//   3. NAT_NONNEG_TRIVIALITY
//   4. NAT_SUB_UNGUARDED
//   5. UNUSED_UNDERSCORE_HYP
//   6. MISALIGNED_DOCSTRING
//   7. ONE_WAY_BOOL_CHECKER
// Strict 7-bit ASCII only (INV-001).

export type ProofFidelityDefectKind =
  | "HYPOTHESIS_ECHO"
  | "REFLEXIVE_TAUTOLOGY"
  | "NAT_NONNEG_TRIVIALITY"
  | "NAT_SUB_UNGUARDED"
  | "UNUSED_UNDERSCORE_HYP"
  | "MISALIGNED_DOCSTRING"
  | "ONE_WAY_BOOL_CHECKER";

export interface ProofFidelityDiagnostic {
  kind: ProofFidelityDefectKind;
  severity: "warning" | "error";
  line: number;
  theoremName: string;
  summary: string;
  remediationHint: string;
}

export interface ProofFidelityAuditReport {
  theoremsScanned: number;
  boolDefsScanned: number;
  diagnostics: ProofFidelityDiagnostic[];
  countsByKind: Record<ProofFidelityDefectKind, number>;
  clean: boolean;
}

interface ParsedBinder {
  names: string[];
  typeText: string;
  bracket: string;
  raw: string;
}

interface ParsedTheoremBlock {
  kind: string;
  name: string;
  line: number;
  signature: string;
  body: string;
  docstring: string;
}

const DOCSTRING_OVERCLAIM_KEYWORDS = [
  "kuratowski",
  "bipartite",
  "quorum",
  "byzantine",
  "non-empty",
  "8 nibbles",
  "bijection",
];

const AUTOMATION_TACTICS = [
  "omega",
  "simp",
  "simpa",
  "nlinarith",
  "linarith",
  "ring",
  "decide",
  "positivity",
  "norm_num",
  "auto",
  "duper",
  "aesop",
  "tauto",
  "trivial",
  "assumption",
  "exact_mod_cast",
  "simp_all",
  "grind",
  "bv_decide",
];

function normalizeWs(s: string): string {
  return s.replace(/\s+/g, " ").trim();
}

function stripOuterParensBalanced(s: string): string {
  let cur = s.trim();
  while (cur.startsWith("(") && cur.endsWith(")")) {
    let depth = 0;
    let balanced = true;
    for (let i = 0; i < cur.length; i++) {
      const ch = cur[i];
      if (ch === "(") depth++;
      else if (ch === ")") {
        depth--;
        if (depth === 0 && i < cur.length - 1) {
          balanced = false;
          break;
        }
      }
    }
    if (balanced && depth === 0) {
      cur = cur.slice(1, -1).trim();
    } else {
      break;
    }
  }
  return cur;
}

function normPropExpr(s: string): string {
  return normalizeWs(stripOuterParensBalanced(s));
}

function stripLeanCommentsPreserveLines(lines: string[]): string[] {
  const out: string[] = [];
  let inBlock = false;
  for (const raw of lines) {
    const chars = raw.split("");
    let i = 0;
    const n = chars.length;
    while (i < n) {
      if (inBlock) {
        if (i + 1 < n && chars[i] === "-" && chars[i + 1] === "/") {
          chars[i] = " ";
          chars[i + 1] = " ";
          inBlock = false;
          i += 2;
          continue;
        }
        chars[i] = " ";
        i++;
        continue;
      }
      if (i + 1 < n && chars[i] === "-" && chars[i + 1] === "-") {
        for (let j = i; j < n; j++) chars[j] = " ";
        break;
      }
      if (i + 1 < n && chars[i] === "/" && chars[i + 1] === "-") {
        inBlock = true;
        chars[i] = " ";
        chars[i + 1] = " ";
        i += 2;
        continue;
      }
      i++;
    }
    out.push(chars.join(""));
  }
  return out;
}

function extractPrecedingDocstring(rawLines: string[], declLine1Based: number): string {
  let idx = declLine1Based - 2;
  while (
    idx >= 0 &&
    (!rawLines[idx].trim() || rawLines[idx].trim().startsWith("@["))
  ) {
    idx--;
  }
  if (idx < 0 || !rawLines[idx].includes("-/")) return "";
  const endIdx = idx;
  let startIdx = endIdx;
  while (startIdx >= 0) {
    if (rawLines[startIdx].includes("/--")) {
      return rawLines.slice(startIdx, endIdx + 1).join("\n");
    }
    const trimmed = rawLines[startIdx].trim();
    if (
      startIdx < endIdx &&
      trimmed &&
      !rawLines[startIdx].startsWith(" ") &&
      !rawLines[startIdx].startsWith("\t")
    ) {
      if (/^(?:theorem|lemma|def|structure|inductive)\b/.test(trimmed)) {
        break;
      }
    }
    startIdx--;
  }
  return "";
}

function isOpenBracket(ch: string): boolean {
  return ch === "(" || ch === "[" || ch === "{" || ch === "\u27e8" || ch === "\u2983";
}

function isCloseBracket(ch: string): boolean {
  return ch === ")" || ch === "]" || ch === "}" || ch === "\u27e9" || ch === "\u2984";
}

function extractTheoremBlocks(sourceText: string): ParsedTheoremBlock[] {
  const rawLines = sourceText.split(/\r?\n/);
  const strippedLines = stripLeanCommentsPreserveLines(rawLines);
  const blocks: ParsedTheoremBlock[] = [];

  const attrPrefix = "(?:@\\[[^\\]]*\\]\\s*)*";
  const modPrefix = "(?:(?:private|protected|public|scoped|noncomputable)\\s+)*";
  const topLevelRe = new RegExp(
    "^" +
      attrPrefix +
      modPrefix +
      "(?:theorem|lemma|example|def|abbrev|instance|structure|inductive|class|end|namespace|section|open|set_option|attribute|#|/--)"
  );
  const declRe = new RegExp(
    "^" + attrPrefix + modPrefix + "(theorem|lemma|example)\\b(?:\\s+(\\S+))?"
  );

  let i = 0;
  while (i < strippedLines.length) {
    const m = strippedLines[i].match(declRe);
    if (!m) {
      i++;
      continue;
    }
    const kind = m[1];
    const rawTok = m[2] || "";
    const name =
      kind === "example"
        ? "(example)"
        : rawTok.split("(")[0].split(":")[0].trim() || "(anonymous)";
    const startLine = i + 1;

    let depth = 0;
    let inString = false;
    let foundAssign = false;
    let assignLine = -1;
    let assignCol = -1;
    const sigLines: string[] = [];
    let j = i;

    while (j < strippedLines.length) {
      const line = strippedLines[j];
      if (j > i && line && line[0] !== " " && line[0] !== "\t" && topLevelRe.test(line)) {
        break;
      }
      for (let k = 0; k < line.length; k++) {
        const ch = line[k];
        if (ch === '"') {
          inString = !inString;
          continue;
        }
        if (inString) continue;
        if (isOpenBracket(ch)) depth++;
        else if (isCloseBracket(ch)) depth = Math.max(0, depth - 1);
        else if (ch === ":" && depth === 0 && k + 1 < line.length && line[k + 1] === "=") {
          foundAssign = true;
          assignLine = j;
          assignCol = k;
          break;
        }
      }
      if (foundAssign) break;
      sigLines.push(line);
      j++;
    }

    if (!foundAssign) {
      i++;
      continue;
    }

    sigLines.push(strippedLines[assignLine].slice(0, assignCol));
    const signature = sigLines.join("\n");

    const bodyLines: string[] = [];
    const remainder = strippedLines[assignLine].slice(assignCol + 2);
    const rstrip = remainder.trim();
    j = assignLine + 1;
    if (/^by\b/.test(rstrip)) {
      const idxBy = remainder.indexOf("by");
      const after = remainder.slice(idxBy + 2);
      if (after.trim()) bodyLines.push(after);
    } else if (rstrip === "") {
      if (j < strippedLines.length && /^by\b/.test(strippedLines[j].trim())) {
        const bl = strippedLines[j];
        const idxBy = bl.indexOf("by");
        const after = bl.slice(idxBy + 2);
        if (after.trim()) bodyLines.push(after);
        j++;
      }
    } else {
      bodyLines.push(remainder);
    }

    while (j < strippedLines.length) {
      const line = strippedLines[j];
      if (line === "" || line[0] === " " || line[0] === "\t") {
        bodyLines.push(line);
        j++;
        continue;
      }
      if (topLevelRe.test(line)) break;
      bodyLines.push(line);
      j++;
    }

    blocks.push({
      kind,
      name,
      line: startLine,
      signature,
      body: bodyLines.join("\n"),
      docstring: extractPrecedingDocstring(rawLines, startLine),
    });
    i = j;
  }

  return blocks;
}

function splitHeaderAndConclusion(signature: string): { header: string; conclusion: string } {
  const leadRe =
    /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|scoped|noncomputable)\s+)*(?:theorem|lemma|example)\b(?:\s+\S+)?/;
  const sig = signature.replace(leadRe, "");
  let depth = 0;
  let inString = false;
  let colonPos = -1;
  for (let i = 0; i < sig.length; i++) {
    const ch = sig[i];
    if (ch === '"') {
      inString = !inString;
      continue;
    }
    if (inString) continue;
    if (isOpenBracket(ch)) depth++;
    else if (isCloseBracket(ch)) depth = Math.max(0, depth - 1);
    else if (ch === ":" && depth === 0) {
      if (i + 1 < sig.length && sig[i + 1] === "=") break;
      colonPos = i;
      break;
    }
  }
  if (colonPos < 0) return { header: sig, conclusion: "" };
  const header = sig.slice(0, colonPos);
  const conclusion = sig.slice(colonPos + 1).replace(/:=[\s\S]*$/, "").trim();
  return { header, conclusion };
}

function extractBinders(signature: string): ParsedBinder[] {
  const { header } = splitHeaderAndConclusion(signature);
  const binders: ParsedBinder[] = [];
  const closeMap: Record<string, string> = {
    "(": ")",
    "{": "}",
    "[": "]",
    "\u2983": "\u2984",
  };
  let j = 0;
  while (j < header.length) {
    const openCh = header[j];
    const closeCh = closeMap[openCh];
    if (closeCh) {
      let depth = 1;
      let k = j + 1;
      let inStr = false;
      let topColon = -1;
      while (k < header.length && depth > 0) {
        const ch = header[k];
        if (ch === '"') inStr = !inStr;
        else if (!inStr) {
          if (ch === openCh) depth++;
          else if (ch === closeCh) {
            depth--;
            if (depth === 0) break;
          } else if (ch === ":" && depth === 1 && topColon < 0) {
            if (k + 1 < header.length && header[k + 1] === "=") k++;
            else topColon = k;
          }
        }
        k++;
      }
      if (depth === 0 && topColon > j) {
        const namesStr = header.slice(j + 1, topColon).trim();
        const typeText = normalizeWs(header.slice(topColon + 1, k));
        const names = namesStr
          .split(/\s+/)
          .filter((tok) => /^[A-Za-z_][A-Za-z0-9_']*$/.test(tok));
        binders.push({
          names,
          typeText,
          bracket: openCh,
          raw: header.slice(j, k + 1),
        });
      }
      j = k + 1;
    } else {
      j++;
    }
  }
  return binders;
}

function findTopLevelEq(text: string): { index: number; op: string } | null {
  let depth = 0;
  let inString = false;
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (ch === '"') {
      inString = !inString;
      continue;
    }
    if (inString) continue;
    if (isOpenBracket(ch)) {
      depth++;
      continue;
    }
    if (isCloseBracket(ch)) {
      depth = Math.max(0, depth - 1);
      continue;
    }
    if (depth !== 0) continue;
    if (text[i] === "\u2194") return { index: i, op: "\u2194" };
    if (text.slice(i, i + 3) === "<->") return { index: i, op: "<->" };
    if (ch === "=") {
      const prev = i > 0 ? text[i - 1] : "";
      const nxt = i + 1 < text.length ? text[i + 1] : "";
      if (":=<>!\u2264\u2265\u2260\u2261\u2194".includes(prev)) continue;
      if (nxt === "=" || nxt === ">") {
        i++;
        continue;
      }
      return { index: i, op: "=" };
    }
  }
  return null;
}

function swapEqSides(expr: string): string | null {
  const clean = normPropExpr(expr);
  const eq = findTopLevelEq(clean);
  if (!eq) return null;
  const lhs = normPropExpr(clean.slice(0, eq.index));
  const rhs = normPropExpr(clean.slice(eq.index + eq.op.length));
  if (!lhs || !rhs) return null;
  return `${rhs} ${eq.op} ${lhs}`;
}

function isValueType(typeStr: string): boolean {
  const t = normPropExpr(typeStr);
  if (
    /(?:=|\u2260|!=|<=|>=|<|>|\u2264|\u2265|\u2194|<->|\u2227|\u2228|\/\\|\\\/|\u2192|->|\bTrue\b|\bFalse\b|\bAnd\b|\bOr\b|\bNot\b|\bProp\b|\u00ac)/.test(
      t
    )
  ) {
    return false;
  }
  const valueHeads = new Set([
    "Nat",
    "\u2115",
    "Int",
    "\u2124",
    "Rat",
    "\u211a",
    "Real",
    "\u211d",
    "Bool",
    "String",
    "Char",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "USize",
    "Float",
    "BitVec",
    "Fin",
    "List",
    "Array",
    "Vector",
    "Option",
    "Finset",
  ]);
  const head = t.split(/\s+/)[0] || "";
  if (valueHeads.has(head)) return true;
  if (
    /^[A-Z][A-Za-z0-9_.]*$/.test(head) &&
    !head.startsWith("Is") &&
    !head.startsWith("Has") &&
    !head.startsWith("WellFormed") &&
    !head.startsWith("Valid") &&
    !head.startsWith("Type") &&
    !head.startsWith("Sort")
  ) {
    return true;
  }
  return false;
}

/**
 * Audit a Lean 4 source file for all 7 specification and vacuity defect classes.
 */
export function auditLeanProofFidelity(sourceText: string): ProofFidelityAuditReport {
  const diagnostics: ProofFidelityDiagnostic[] = [];
  const countsByKind: Record<ProofFidelityDefectKind, number> = {
    HYPOTHESIS_ECHO: 0,
    REFLEXIVE_TAUTOLOGY: 0,
    NAT_NONNEG_TRIVIALITY: 0,
    NAT_SUB_UNGUARDED: 0,
    UNUSED_UNDERSCORE_HYP: 0,
    MISALIGNED_DOCSTRING: 0,
    ONE_WAY_BOOL_CHECKER: 0,
  };

  const pushDiag = (d: ProofFidelityDiagnostic) => {
    diagnostics.push(d);
    countsByKind[d.kind] = (countsByKind[d.kind] || 0) + 1;
  };

  const theoremBlocks = extractTheoremBlocks(sourceText);

  for (const thm of theoremBlocks) {
    const { conclusion: rawConclusion } = splitHeaderAndConclusion(thm.signature);
    const conclusion = normPropExpr(rawConclusion);
    const binders = extractBinders(thm.signature);
    const bodyLines = thm.body
      .split(/\r?\n/)
      .map((l) => l.trim())
      .filter((l) => l.length > 0 && !l.startsWith("--"));
    const bodyNormRaw = normalizeWs(bodyLines.join(" "));
    const bodyNorm = bodyNormRaw.startsWith("by ")
      ? bodyNormRaw.slice(3).trim()
      : bodyNormRaw;

    // 1. HYPOTHESIS_ECHO
    if (conclusion && binders.length > 0) {
      const hypTypes = binders.map((b) => normPropExpr(b.typeText)).filter(Boolean);
      const echoCloser =
        bodyNorm === "assumption" ||
        bodyNorm === "trivial" ||
        /^(?:exact\s+)?(?:[A-Za-z_][A-Za-z0-9_']*(?:\.(?:symm|mp|mpr|left|right|1|2))?|\u27e8\s*[A-Za-z0-9_'.\s,]+\s*\u27e9|And\.intro\s+[A-Za-z0-9_'.]+\s+[A-Za-z0-9_'.]+|Eq\.symm\s+[A-Za-z0-9_'.]+)$/.test(
          bodyNorm
        );
      if (echoCloser) {
        let echoed: string | null = null;
        for (const ht of hypTypes) {
          if (conclusion === ht) {
            echoed = `Conclusion \`${conclusion}\` directly echoes hypothesis \`${ht}\` via \`${bodyNorm}\`.`;
            break;
          }
          const swapped = swapEqSides(ht);
          if (swapped && conclusion === swapped) {
            echoed = `Conclusion \`${conclusion}\` is a direct symmetric echo of hypothesis \`${ht}\` via \`${bodyNorm}\`.`;
            break;
          }
          for (const sep of ["\u2227", "/\\"]) {
            if (ht.includes(sep)) {
              const parts = ht.split(sep).map((p) => normPropExpr(p));
              if (parts.includes(conclusion)) {
                echoed = `Conclusion \`${conclusion}\` projects conjunct directly from hypothesis \`${ht}\` via \`${bodyNorm}\`.`;
                break;
              }
            }
          }
          if (echoed) break;
        }
        if (!echoed) {
          for (const sep of ["\u2227", "/\\"]) {
            if (conclusion.includes(sep)) {
              const cParts = conclusion
                .split(sep)
                .map((p) => normPropExpr(p))
                .filter(Boolean);
              if (cParts.length > 0 && cParts.every((cp) => hypTypes.includes(cp))) {
                echoed = `Conjunction conclusion \`${conclusion}\` directly echoes hypotheses via \`${bodyNorm}\`.`;
                break;
              }
            }
          }
        }
        if (echoed) {
          pushDiag({
            kind: "HYPOTHESIS_ECHO",
            severity: "warning",
            line: thm.line,
            theoremName: thm.name,
            summary: echoed,
            remediationHint:
              "Replace the echoed hypothesis with the underlying constructive definition or state a non-trivial consequence.",
          });
        }
      }
    }

    // 2. REFLEXIVE_TAUTOLOGY
    if (
      conclusion &&
      ["rfl", "exact rfl", "Eq.refl", "Iff.rfl", "exact Iff.rfl"].includes(bodyNorm)
    ) {
      const eq = findTopLevelEq(conclusion);
      let isRefl = false;
      if (eq) {
        const lhs = normPropExpr(conclusion.slice(0, eq.index));
        const rhs = normPropExpr(conclusion.slice(eq.index + eq.op.length));
        if (lhs && lhs === rhs) isRefl = true;
      }
      if (!isRefl) {
        const beqMatch = conclusion.match(
          /^\(?(.+?)\s*==\s*(.+?)\)?\s*=\s*\(?(.+?)\s*==\s*(.+?)\)?$/
        );
        if (
          beqMatch &&
          normPropExpr(beqMatch[1]) === normPropExpr(beqMatch[3]) &&
          normPropExpr(beqMatch[2]) === normPropExpr(beqMatch[4])
        ) {
          isRefl = true;
        }
      }
      if (isRefl) {
        pushDiag({
          kind: "REFLEXIVE_TAUTOLOGY",
          severity: "warning",
          line: thm.line,
          theoremName: thm.name,
          summary: `Conclusion \`${conclusion}\` is syntactically reflexive (\`lhs = lhs\`) and closed by \`rfl\`.`,
          remediationHint:
            "Relate two distinct definitions or an implementation and its specification rather than asserting `e = e`.",
        });
      }
    }

    // 3. NAT_NONNEG_TRIVIALITY
    const natVars = new Set<string>();
    for (const b of binders) {
      if (b.typeText === "Nat" || b.typeText === "\u2115") {
        for (const n of b.names) natVars.add(n);
      }
    }
    if (conclusion && (natVars.size > 0 || /\b(?:Nat|\u2115)\b/.test(thm.signature))) {
      const mGe = conclusion.match(/^(.+?)\s*(?:>=|\u2265)\s*0$/);
      const mLe = conclusion.match(/^0\s*(?:<=|\u2264)\s*(.+)$/);
      const expr = normPropExpr(mGe ? mGe[1] : mLe ? mLe[1] : "");
      if (
        expr &&
        !expr.includes("Finset.sum") &&
        !expr.includes("\u2211") &&
        !/\b(?:Real|\u211d|Int|\u2124|Rat|\u211a)\b/.test(thm.signature)
      ) {
        const toks = expr.match(/\b[A-Za-z_][A-Za-z0-9_']*\b/g) || [];
        if (toks.some((t) => natVars.has(t)) || /\bNat\./.test(expr)) {
          pushDiag({
            kind: "NAT_NONNEG_TRIVIALITY",
            severity: "warning",
            line: thm.line,
            theoremName: thm.name,
            summary: `Conclusion \`${conclusion}\` asserts \`>= 0\` over \`Nat\`, which holds trivially by type construction.`,
            remediationHint:
              "State a positive lower bound (`>= 1`), an exact conservation identity, or cast to `Int` if signed values are intended.",
          });
        }
      }
    }

    // 4. NAT_SUB_UNGUARDED
    if (conclusion && natVars.size > 0) {
      const propClauses: string[] = [];
      for (const b of binders) {
        if (!isValueType(b.typeText)) propClauses.push(b.typeText);
      }
      const arrowParts = conclusion.split(/\u2192|->/);
      for (const part of arrowParts) {
        if (part.trim()) propClauses.push(part.trim());
      }
      let reportedSub = false;
      for (let cIdx = 0; cIdx < propClauses.length && !reportedSub; cIdx++) {
        const clause = propClauses[cIdx];
        const otherHyps = propClauses
          .filter((_, idx) => idx !== cIdx)
          .join(" ; ");
        const subRe = /\b([A-Za-z_][A-Za-z0-9_']*)\s*-\s*([A-Za-z_][A-Za-z0-9_']*|\d+)\b/g;
        let sm: RegExpExecArray | null;
        while ((sm = subRe.exec(clause)) !== null) {
          const lhs = sm[1];
          const rhs = sm[2];
          if (!natVars.has(lhs) || rhs === "0" || lhs === rhs) continue;
          const guardRes = [
            new RegExp(`\\b${rhs}\\b[^;]*(?:<=|\\u2264|<)\\s*[^;]*\\b${lhs}\\b`),
            new RegExp(`\\b${lhs}\\b[^;]*(?:>=|\\u2265|>)\\s*[^;]*\\b${rhs}\\b`),
          ];
          if (/^\d+$/.test(rhs)) {
            guardRes.push(new RegExp(`\\b${lhs}\\b[^;]*(?:>=|\\u2265|>)\\s*\\d+`));
            guardRes.push(new RegExp(`\\d+\\s*(?:<=|\\u2264|<)\\s*[^;]*\\b${lhs}\\b`));
            guardRes.push(new RegExp(`\\b${lhs}\\s*(?:!=|\\u2260)\\s*0`));
            guardRes.push(new RegExp(`0\\s*<\\s*\\b${lhs}\\b`));
          }
          if (!guardRes.some((r) => r.test(otherHyps))) {
            pushDiag({
              kind: "NAT_SUB_UNGUARDED",
              severity: "warning",
              line: thm.line,
              theoremName: thm.name,
              summary: `Unguarded Nat subtraction \`${lhs} - ${rhs}\` in \`${clause}\` without \`${rhs} <= ${lhs}\` hypothesis.`,
              remediationHint: `Add hypothesis \`(h : ${rhs} <= ${lhs})\` or rewrite in additive form \`${lhs} = ... + ${rhs}\` to prevent truncating subtraction at 0.`,
            });
            reportedSub = true;
            break;
          }
        }
      }
    }

    // 5. UNUSED_UNDERSCORE_HYP (including unused value binders even when omega/simp/decide is used)
    const hasAutomation =
      AUTOMATION_TACTICS.some((t) => new RegExp(`\\b${t}\\b`).test(thm.body)) ||
      thm.body.includes("unfold");
    for (let bIdx = 0; bIdx < binders.length; bIdx++) {
      const b = binders[bIdx];
      const isVal = isValueType(b.typeText);
      for (const name of b.names) {
        if (name === "_") continue;
        const isUnderscore = name.startsWith("_");
        if (b.bracket !== "(" && !isUnderscore) continue;
        if (name.length === 1 && !isVal && !isUnderscore) continue;
        const wordRe = new RegExp(`(?<![A-Za-z0-9_'])${name}(?![A-Za-z0-9_'])`);
        if (wordRe.test(rawConclusion)) continue;
        let usedInOther = false;
        for (let oIdx = 0; oIdx < binders.length; oIdx++) {
          if (oIdx === bIdx) continue;
          if (wordRe.test(binders[oIdx].typeText)) {
            usedInOther = true;
            break;
          }
        }
        if (usedInOther) continue;
        if (wordRe.test(thm.body)) continue;
        if (isUnderscore || isVal || !hasAutomation) {
          pushDiag({
            kind: "UNUSED_UNDERSCORE_HYP",
            severity: "warning",
            line: thm.line,
            theoremName: thm.name,
            summary: `Binder \`${name} : ${b.typeText}\` is never referenced in the conclusion, other binder types, or proof body.`,
            remediationHint:
              "Remove the dead hypothesis/value binder or tighten the conclusion so it genuinely depends on the parameter.",
          });
        }
      }
    }

    // 6. MISALIGNED_DOCSTRING
    if (thm.docstring && bodyLines.length === 1) {
      const docLower = thm.docstring.toLowerCase();
      const matchedKw = DOCSTRING_OVERCLAIM_KEYWORDS.filter((kw) => docLower.includes(kw));
      if (
        matchedKw.length > 0 &&
        ["rfl", "omega", "decide", "trivial"].includes(bodyNorm) &&
        ![
          "\u2200",
          "\u2203",
          "\u2194",
          "\u2227",
          "\u2228",
          "Finset",
          "Set",
          "Graph",
          "Bijective",
        ].some((q) => conclusion.includes(q))
      ) {
        pushDiag({
          kind: "MISALIGNED_DOCSTRING",
          severity: "warning",
          line: thm.line,
          theoremName: thm.name,
          summary: `Docstring claims domain property (${matchedKw.join(", ")}) while \`${conclusion}\` is a 1-line \`${bodyNorm}\` equality/inequality.`,
          remediationHint:
            "Align the docstring with the actual arithmetic lemma or strengthen the theorem statement to formalize the claimed domain property.",
        });
      }
    }
  }

  // 7. ONE_WAY_BOOL_CHECKER
  const strippedText = stripLeanCommentsPreserveLines(sourceText.split(/\r?\n/)).join("\n");
  const defRe =
    /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|public|scoped|noncomputable)\s+)*def\s+([A-Za-z_][A-Za-z0-9_']*)\b[\s\S]*?:\s*Bool\s*:=/gm;
  const boolDefs = new Map<string, number>();
  let dm: RegExpExecArray | null;
  while ((dm = defRe.exec(strippedText)) !== null) {
    const spanText = dm[0];
    const declCount = (
      spanText.match(/^\s*(?:def|theorem|lemma|structure|inductive)\b/gm) || []
    ).length;
    if (declCount > 1) continue;
    const fnName = dm[1];
    const lineNo = strippedText.slice(0, dm.index).split("\n").length;
    boolDefs.set(fnName, lineNo);
  }

  for (const [fnName, defLine] of boolDefs.entries()) {
    const fnPat = new RegExp(`\\b${fnName}\\b`);
    const oneWaySoundness: ParsedTheoremBlock[] = [];
    let hasIffOrComplete = false;
    for (const thm of theoremBlocks) {
      if (!fnPat.test(thm.signature)) continue;
      const { conclusion } = splitHeaderAndConclusion(thm.signature);
      const concNorm = normPropExpr(conclusion);
      if (
        thm.signature.includes("\u2194") ||
        thm.signature.includes("<->") ||
        /\bIff\b/.test(thm.signature) ||
        thm.name.endsWith("_iff")
      ) {
        hasIffOrComplete = true;
        break;
      }
      for (const arrow of ["\u2192", "->"]) {
        if (concNorm.includes(arrow)) {
          const parts = concNorm.split(arrow).map((p) => p.trim());
          const lhsParts = parts.slice(0, -1).join(" -> ");
          const rhs = parts[parts.length - 1] || "";
          const inBinders = extractBinders(thm.signature).some((b) => fnPat.test(b.typeText));
          if (fnPat.test(rhs) && !fnPat.test(lhsParts) && !inBinders) {
            hasIffOrComplete = true;
            break;
          }
        }
      }
      if (hasIffOrComplete) break;
      if (
        new RegExp(`\\b${fnName}\\b[\\s\\S]*?=\\s*false`).test(thm.signature) &&
        extractBinders(thm.signature).length > 0
      ) {
        hasIffOrComplete = true;
        break;
      }
      if (new RegExp(`\\b${fnName}\\b[\\s\\S]*?=\\s*true`).test(thm.signature)) {
        oneWaySoundness.push(thm);
      }
    }
    if (oneWaySoundness.length > 0 && !hasIffOrComplete) {
      const firstThm = oneWaySoundness[0];
      pushDiag({
        kind: "ONE_WAY_BOOL_CHECKER",
        severity: "warning",
        line: firstThm.line,
        theoremName: firstThm.name,
        summary: `Executable Bool checker \`${fnName}\` (line ${defLine}) only has one-way soundness (\`${firstThm.name}\`) without a companion \`<->\` (\`iff\`) or completeness theorem.`,
        remediationHint: `State and prove \`${fnName} ... = true <-> Spec ...\` (Check 5 necessity & sufficiency pairing) so a constant-false implementation cannot pass.`,
      });
    }
  }

  return {
    theoremsScanned: theoremBlocks.length,
    boolDefsScanned: boolDefs.size,
    diagnostics,
    countsByKind,
    clean: diagnostics.length === 0,
  };
}
