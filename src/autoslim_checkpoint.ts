// Durable optimization hints. Journal contents never replace a fresh final check.
import * as fs from "node:fs";
import * as path from "node:path";
import { createHash, randomUUID } from "node:crypto";

export interface VerificationVerdict {
  ok: boolean;
  errorCount: number;
  warningCount: number;
  firstIssue?: string;
  inconclusive?: boolean;
}
export function verificationInconclusive(v: VerificationVerdict): boolean {
  return v.inconclusive === true || /timeout|timed out|analysis_incomplete|environment_unavailable|spawn failed|ENOENT|EACCES|document-not-open|LSP.*(?:version|did not complete)/i.test(v.firstIssue || "");
}
export function assertNoSymlinkComponents(target: string): void {
  let current = path.parse(path.resolve(target)).root;
  for (const component of path.resolve(target).slice(current.length).split(path.sep).filter(Boolean)) {
    current = path.join(current, component);
    try { if (fs.lstatSync(current).isSymbolicLink()) throw new Error(`Refusing symlink path component: ${current}`); }
    catch (error: any) { if (error.code === "ENOENT") return; throw error; }
  }
}
export type VerificationStage = "group" | "single" | "final";
export const contentHash = (text: string | Buffer): string => createHash("sha256").update(text).digest("hex");

export class AutoSlimJournal {
  readonly filePath: string;
  readonly verdicts = new Map<string, VerificationVerdict>();
  readonly accepted = new Map<string, string>();
  readonly pendingAttempts = new Set<string>();
  private readonly identity: string;

  constructor(directory: string, identity: string, fresh = false) {
    this.identity = identity;
    assertNoSymlinkComponents(directory);
    if (fs.existsSync(directory) && fs.lstatSync(directory).isSymbolicLink()) {
      throw new Error("Refusing symlink checkpoint directory");
    }
    fs.mkdirSync(directory, { recursive: true });
    assertNoSymlinkComponents(directory);
    this.filePath = path.join(directory, `${identity}.jsonl`);
    if (fs.existsSync(this.filePath)) {
      if (fs.lstatSync(this.filePath).isSymbolicLink() || !fs.statSync(this.filePath).isFile()) {
        throw new Error("Refusing symlink or non-regular checkpoint journal");
      }
      if (fresh) fs.renameSync(this.filePath, this.filePath + ".archived-" + randomUUID());
    }
    if (fs.existsSync(this.filePath)) {
      if (fs.statSync(this.filePath).size > 64 * 1024 * 1024) throw new Error("Invalid checkpoint journal size");
      const bytes = fs.readFileSync(this.filePath);
      const end = bytes.lastIndexOf(10) + 1;
      const committed = bytes.subarray(0, end);
      if (!Buffer.from(committed.toString("utf8")).equals(committed)) throw new Error("Invalid checkpoint journal UTF-8");
      for (const line of bytes.subarray(0, end).toString("utf8").split("\n").filter(Boolean)) {
        let record: any;
        try { record = JSON.parse(line); } catch { throw new Error("Corrupt checkpoint journal record"); }
        this.replay(record);
      }
      // An interrupted final append has no completed verdict. Heal only that tail.
      if (end < bytes.length) fs.truncateSync(this.filePath, end);
    }
    if (fresh) this.append({ event: "reset" });
  }

  private replay(record: any): void {
    if (!record || record.schemaVersion !== 1 || record.identity !== this.identity) {
      throw new Error("Checkpoint journal identity/schema mismatch");
    }
    if (record.event === "reset") {
      this.verdicts.clear(); this.accepted.clear(); this.pendingAttempts.clear(); return;
    }
    if (record.event === "start") {
      if (typeof record.attemptId !== "string") throw new Error("Invalid checkpoint attempt record");
      this.pendingAttempts.add(record.attemptId); return;
    }
    if (record.event === "accepted") {
      if (typeof record.candidateId !== "string" || typeof record.tactic !== "string") {
        throw new Error("Invalid checkpoint candidate record");
      }
      this.accepted.set(record.candidateId, record.tactic); return;
    }
    if (record.event === "attempt") {
      const v = record.verdict;
      if (!/^[a-f0-9]{64}$/.test(record.contentHash) || typeof record.attemptId !== "string"
        || !["group", "single", "final"].includes(record.stage)
        || !v || typeof v.ok !== "boolean" || !Number.isInteger(v.errorCount) || v.errorCount < 0
        || !Number.isInteger(v.warningCount) || v.warningCount < 0
        || (v.ok && (v.errorCount !== 0 || v.warningCount !== 0))
        || (v.firstIssue !== undefined && typeof v.firstIssue !== "string")) {
        throw new Error("Invalid checkpoint verification record");
      }
      this.pendingAttempts.delete(record.attemptId);
      const transient = /timeout|analysis_incomplete|environment_unavailable|spawn failed|LSP.*version/i.test(v.firstIssue || "");
      if (record.stage !== "final" && !verificationInconclusive(v)) this.verdicts.set(record.contentHash, v);
      if (record.acceptedCandidates !== undefined) {
        if (!v.ok || v.errorCount || v.warningCount || record.stage === "final"
          || !Array.isArray(record.acceptedCandidates) || record.acceptedCandidates.some((p: any) => !Array.isArray(p) || p.length !== 2 || p.some((s: any) => typeof s !== "string"))) throw new Error("Invalid checkpoint group decisions");
        for (const [id,tactic] of record.acceptedCandidates) this.accepted.set(id,tactic);
      }
      return;
    }
    throw new Error("Unknown checkpoint journal record");
  }

  private append(payload: Record<string, unknown>): void {
    const record = { schemaVersion: 1, identity: this.identity, ...payload };
    const flags = fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_APPEND
      | (fs.constants.O_NOFOLLOW || 0);
    const fd = fs.openSync(this.filePath, flags, 0o600);
    try { fs.writeFileSync(fd, JSON.stringify(record) + "\n", "utf8"); fs.fsyncSync(fd); }
    finally { fs.closeSync(fd); }
    this.replay(record);
  }

  start(stage: VerificationStage, hash: string): string {
    const attemptId = randomUUID();
    this.append({ event: "start", attemptId, stage, contentHash: hash });
    return attemptId;
  }
  finish(attemptId: string, stage: VerificationStage, hash: string, verdict: VerificationVerdict, elapsedMs: number, acceptedCandidates?: [string,string][]): void {
    this.append({ event: "attempt", attemptId, stage, contentHash: hash, verdict, elapsedMs, ...(acceptedCandidates ? {acceptedCandidates}: {}) });
  }
  accept(candidateId: string, tactic: string): void {
    this.append({ event: "accepted", candidateId, tactic });
  }
}
