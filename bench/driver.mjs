// /tmp/verb-bench/driver.mjs
// bench/driver.mjs - the tranche-4 benchmark protocol: stdio JSON-RPC
// against the real server, six statements x three runs, one forced
// budget_expired, one duplicate pair. Run: npm run bench
// (env LEAN_LSP_BENCH_PROJECT overrides the Lean project cwd).
// TIMING GATE: absolute numbers are only valid in a quiet window
// (no concurrent lake/blueprint mass-edit lanes); under load they are
// relative-only. Record every run in bench/README.md.
import { spawn } from "node:child_process";
import * as fs from "node:fs";

import * as path from "node:path";
import { fileURLToPath } from "node:url";
const LSP_DIR = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const PROJECT = process.env.LEAN_LSP_BENCH_PROJECT ?? "/home/radu/code/tacit-mui/docs/easci/lean";
const CORPUS = path.join(LSP_DIR, "bench", "corpus.lean");

const server = spawn(
  process.execPath,
  ["--experimental-strip-types", `${LSP_DIR}/src/index.ts`],
  { cwd: PROJECT, stdio: ["pipe", "pipe", "pipe"] }
);

let buf = "";
const pending = new Map();
let nextId = 1;
const stderrChunks = [];

server.stdout.on("data", (d) => {
  buf += d.toString("utf-8");
  let i;
  while ((i = buf.indexOf("\n")) !== -1) {
    const line = buf.slice(0, i).trim();
    buf = buf.slice(i + 1);
    if (!line) continue;
    let msg;
    try { msg = JSON.parse(line); } catch { continue; }
    const h = pending.get(msg.id);
    if (h) { pending.delete(msg.id); h(msg); }
  }
});
server.stderr.on("data", (d) => stderrChunks.push(d.toString("utf-8")));

function rpc(method, params) {
  const id = nextId++;
  return new Promise((resolve) => {
    pending.set(id, resolve);
    server.stdin.write(JSON.stringify({ jsonrpc: "2.0", id, method, params }) + "\n");
  });
}

async function callVerb(args) {
  const t0 = Date.now();
  const res = await rpc("tools/call", { name: "lean_counterexample_search", arguments: args });
  const dt = Date.now() - t0;
  let text = "";
  if (res.error) text = `RPC-ERROR: ${res.error.message}`;
  else text = res.result?.content?.[0]?.text ?? "(no text)";
  const firstLine = text.split("\n")[0];
  const state = firstLine.startsWith("counterexample") ? "counterexample"
    : firstLine.startsWith("survived") ? "survived"
    : firstLine.startsWith("budget_expired") ? "budget_expired"
    : firstLine.startsWith("unsupported") ? "unsupported"
    : "UNKNOWN";
  return { dt, state, firstLine: firstLine.slice(0, 150) };
}

const STMTS = ["s1_add_comm", "s2_lt_three", "s3_two_mul", "s4_pow_bound", "s5_reverse_reverse", "s6_abstract"];
const results = [];
const tStart = Date.now();

const init = await rpc("initialize", {
  protocolVersion: "2024-11-05",
  capabilities: {},
  clientInfo: { name: "verb-bench", version: "1.0" },
});
console.log("initialize:", JSON.stringify(init).slice(0, 200));

for (const s of STMTS) {
  for (let run = 1; run <= 3; run++) {
    const r = await callVerb({ filePath: CORPUS, theoremName: s, imports: ["Mathlib"] });
    results.push({ phase: "main", stmt: s, run, ...r });
    console.log(`[main] ${s} #${run}: ${r.state} ${r.dt}ms | ${r.firstLine}`);
  }
}

// Forced budget_expired: tiny budget under the per-run import cost.
{
  const r = await callVerb({ filePath: CORPUS, theoremName: "s5_reverse_reverse", imports: ["Mathlib"], samples: 10000, budgetMs: 1500 });
  results.push({ phase: "budget", stmt: "s5_reverse_reverse", run: 1, ...r });
  console.log(`[budget] s5 budgetMs=1500 samples=10000: ${r.state} ${r.dt}ms | ${r.firstLine}`);
}

// Duplicate pair (same args fired together). Note: the stdio server loop
// dispatches messages sequentially, so key-sharing is not observable
// here; the in-process unit suite pins the single-flight path.
{
  const [a, b] = await Promise.all([
    callVerb({ filePath: CORPUS, theoremName: "s3_two_mul", imports: ["Mathlib"] }),
    callVerb({ filePath: CORPUS, theoremName: "s3_two_mul", imports: ["Mathlib"] }),
  ]);
  results.push({ phase: "duplicate", stmt: "s3_two_mul", run: 1, ...a });
  results.push({ phase: "duplicate", stmt: "s3_two_mul", run: 2, ...b });
  console.log(`[dup] s3 A: ${a.state} ${a.dt}ms; B: ${b.state} ${b.dt}ms; identical=${a.firstLine === b.firstLine}`);
}

fs.writeFileSync(path.join(LSP_DIR, "bench", "results.json"), JSON.stringify({
  totalWallMs: Date.now() - tStart,
  results,
  stderrTail: stderrChunks.join("").split("\n").slice(-8),
}, null, 1));

console.log("\n=== summary (main phase, 3 runs each; timings relative under load) ===");
const by = {};
for (const r of results.filter((r) => r.phase === "main")) {
  (by[r.stmt] ??= []).push(r);
}
for (const [s, rs] of Object.entries(by)) {
  console.log(`${s.padEnd(20)} states=${rs.map((r) => r.state).join(",")} times=${rs.map((r) => r.dt + "ms").join(",")}`);
}
console.log(`total wall: ${((Date.now() - tStart) / 1000).toFixed(1)}s`);

server.stdin.end();
setTimeout(() => process.exit(0), 1500);
