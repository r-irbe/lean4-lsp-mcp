// Optional bounded observations influence ordering only, never verification.
import * as fs from "node:fs";
export interface RankingObservation { route: string; tactic: string; ok: boolean; elapsedMs: number; }
export function readRankingHistory(file?: string): RankingObservation[] {
  if (!file) return [];
  const limit = 4 * 1024 * 1024;
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NONBLOCK);
  let text: string;
  try {
    const stat = fs.fstatSync(fd);
    if (!stat.isFile() || stat.size > limit) throw new Error("Invalid ranking history file or size");
    const buffer = Buffer.alloc(limit + 1);
    let used = 0, count: number;
    while (used < buffer.length && (count = fs.readSync(fd, buffer, used, buffer.length - used, null)) > 0) used += count;
    if (used > limit) throw new Error("Invalid ranking history size");
    text = buffer.subarray(0, used).toString("utf8");
  } finally { fs.closeSync(fd); }
  const value = JSON.parse(text);
  if (value && value.observations === undefined) value.observations = value.rankingObservations;
  if (value?.schemaVersion !== 1 || !Array.isArray(value.observations) || value.observations.length > 10000
    || value.observations.some((o: any) => !o || typeof o.route !== "string" || o.route.length > 200
      || typeof o.tactic !== "string" || o.tactic.length > 4096 || typeof o.ok !== "boolean"
      || typeof o.elapsedMs !== "number" || !Number.isFinite(o.elapsedMs) || o.elapsedMs < 0)) {
    throw new Error("Invalid ranking history observations");
  }
  return value.observations;
}
function utility(observations: RankingObservation[]): number {
  if (!observations.length) return 1;
  // Neutral prior: one success and one failure at one second each. Bound the
  // influence of a small sample or an unrepresentative expensive observation.
  const successes = observations.filter(o => o.ok).length;
  const cost = (2000 + observations.reduce((n,o) => n + Math.min(120000,Math.max(1,o.elapsedMs)),0)) / (observations.length + 2);
  return Math.max(0.1,Math.min(10, ((successes + 1) / (observations.length + 2)) * 2000 / cost));
}
export function rankTactics(route: string, tactics: string[], history: RankingObservation[]): string[] {
  return tactics.map((tactic,index) => ({tactic,index,score:utility(history.filter(o=>o.route===route && o.tactic===tactic))}))
    .sort((a,b)=>b.score-a.score || a.index-b.index).map(o=>o.tactic);
}
export function candidatePriority(route: string, saving: number, history: RankingObservation[]): number {
  return saving * utility(history.filter(o=>o.route===route));
}
