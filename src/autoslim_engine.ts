// Cumulative grouped verification: a cached verdict is only a hint until final compilation.
import { AutoSlimJournal, contentHash, verificationInconclusive, type VerificationVerdict, type VerificationStage } from "./autoslim_checkpoint.ts";

export interface ProofProposal {
  id: string;
  tactics: string[];
}
export interface GroupedVerificationResult {
  accepted: Map<string, string>;
  rejected: Map<string, { triedTactics: string[]; lastDiagnostic?: string }>;
  completed: boolean;
  stopReason?: "attempt-budget" | "final-check-failed" | "verification-inconclusive";
  stopDiagnostic?: string;
  resumedCandidates: number;
  cacheHits: number;
  groupChecks: number;
  bisections: number;
  finalCheckPassed: boolean | null;
  attempts: number;
  verificationTimeMs: number;
  observations: { id: string; tactic: string; ok: boolean; elapsedMs: number }[];
}

class AttemptBudget extends Error {}
class InconclusiveVerification extends Error {}

export async function verifyProofGroups(options: {
  proposals: ProofProposal[];
  render: (accepted: ReadonlyMap<string, string>) => string;
  verify: (content: string) => Promise<VerificationVerdict>;
  journal: AutoSlimJournal;
  groupSize: number;
  maxAttempts?: number;
}): Promise<GroupedVerificationResult> {
  const accepted = new Map<string, string>();
  const rejected: GroupedVerificationResult["rejected"] = new Map();
  let attempts = 0, cacheHits = 0, groupChecks = 0, bisections = 0, verificationTimeMs = 0;
  const observations: GroupedVerificationResult["observations"] = [];
  let finalCheckPassed: boolean | null = null;
  for (const p of options.proposals) {
    const saved = options.journal.accepted.get(p.id);
    if (saved !== undefined) {
      if (!p.tactics.includes(saved)) throw new Error("Checkpoint candidate no longer matches an allowed recipe");
      accepted.set(p.id, saved);
    }
  }
  const resumedCandidates = accepted.size;
  const strict = (v: VerificationVerdict) => v.ok && v.errorCount === 0 && v.warningCount === 0;
  const check = async (content: string, stage: VerificationStage, decisions?: [string,string][]): Promise<VerificationVerdict> => {
    const hash = contentHash(content);
    if (stage !== "final") {
      const cached = options.journal.verdicts.get(hash);
      if (cached) { cacheHits++; return cached; }
    }
    if (options.maxAttempts !== undefined && attempts >= options.maxAttempts) throw new AttemptBudget();
    const attemptId = options.journal.start(stage, hash);
    attempts++;
    const start = performance.now();
    const raw = await options.verify(content);
    const verdict = { ...raw, ok: strict(raw) && !verificationInconclusive(raw) };
    const elapsed = performance.now() - start;
    verificationTimeMs += elapsed;
    options.journal.finish(attemptId, stage, hash, verdict, elapsed, verdict.ok && stage !== "final" ? decisions : undefined);
    if (verificationInconclusive(verdict)) throw new InconclusiveVerification(verdict.firstIssue || "Verifier could not complete");
    return verdict;
  };
  const commit = (p: ProofProposal, tactic: string) => {
    options.journal.accept(p.id, tactic);
    accepted.set(p.id, tactic);
  };
  const group = async (items: ProofProposal[]): Promise<void> => {
    if (items.length === 0) return;
    const trial = new Map(accepted);
    for (const p of items) trial.set(p.id, p.tactics[0]);
    groupChecks++;
    const beforeAttempts = attempts, beforeTime = verificationTimeMs;
    const initial = await check(options.render(trial), items.length > 1 ? "group" : "single", items.map(p=>[p.id,p.tactics[0]]));
    if (items.length === 1 && attempts > beforeAttempts) observations.push({ id: items[0].id, tactic: items[0].tactics[0], ok: strict(initial), elapsedMs: verificationTimeMs - beforeTime });
    if (strict(initial)) { for (const p of items) commit(p, p.tactics[0]); return; }
    if (items.length > 1) {
      bisections++;
      const mid = Math.floor(items.length / 2);
      await group(items.slice(0, mid));
      await group(items.slice(mid));
      return;
    }
    const p = items[0];
    const triedTactics = [p.tactics[0]];
    let lastDiagnostic = initial.firstIssue;
    for (const tactic of p.tactics.slice(1)) {
      const next = new Map(accepted); next.set(p.id, tactic);
      triedTactics.push(tactic);
      const beforeAttempts = attempts, beforeTime = verificationTimeMs;
      const verdict = await check(options.render(next), "single", [[p.id,tactic]]);
      if (attempts > beforeAttempts) observations.push({id:p.id,tactic,ok:strict(verdict),elapsedMs:verificationTimeMs-beforeTime});
      if (strict(verdict)) { commit(p, tactic); return; }
      lastDiagnostic = verdict.firstIssue;
    }
    rejected.set(p.id, { triedTactics, ...(lastDiagnostic ? { lastDiagnostic } : {}) });
  };

  let stopReason: GroupedVerificationResult["stopReason"];
  let stopDiagnostic: string | undefined;
  try {
    const pending = options.proposals.filter(p => !accepted.has(p.id));
    for (let i = 0; i < pending.length; i += options.groupSize) {
      await group(pending.slice(i, i + options.groupSize));
    }
    if (accepted.size > 0) {
      finalCheckPassed = strict(await check(options.render(accepted), "final"));
      if (!finalCheckPassed) stopReason = "final-check-failed";
    }
  } catch (error) {
    if (error instanceof AttemptBudget) stopReason = "attempt-budget";
    else if (error instanceof InconclusiveVerification) { stopReason = "verification-inconclusive"; stopDiagnostic = error.message; }
    else throw error;
  }
  return { accepted, rejected, completed: !stopReason, ...(stopReason ? { stopReason } : {}), ...(stopDiagnostic ? {stopDiagnostic} : {}),
    resumedCandidates, cacheHits, groupChecks, bisections, finalCheckPassed, attempts, verificationTimeMs, observations };
}
