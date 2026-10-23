// /tmp/verb-bench/dense_probe.mjs (re-created after the freeze blocked its first write)
// Post-implementation verification on the real server (stdio):
//   A. far_stmt slice  -> survived (the v1-unproductive pin)
//   B. far_stmt dense  -> counterexample via sized-wide, wall measured
//   C. far_stmt budget -> budget_expired with the wall near the budget
//      (the process-group kill closes the 7.1s/1.5s overrun)
import { spawn } from "node:child_process";

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
  const text = res.error ? `RPC-ERROR: ${res.error.message}` : (res.result?.content?.[0]?.text ?? "(no text)");
  return { dt, text };
}

await rpc("initialize", { protocolVersion: "2024-11-05", capabilities: {}, clientInfo: { name: "dense-probe", version: "1.0" } });

console.log("--- A: slice on far_stmt (expect survived) ---");
{
  const r = await callVerb({ filePath: CORPUS, theoremName: process.env.LEAN_LSP_BENCH_FAR ?? "far_stmt", imports: ["Mathlib"] });
  console.log(`wall=${r.dt}ms first-line: ${r.text.split("\n")[0]}`);
}
console.log("--- B: dense on far_stmt (expect counterexample, sized-wide) ---");
{
  const r = await callVerb({ filePath: CORPUS, theoremName: process.env.LEAN_LSP_BENCH_FAR ?? "far_stmt", imports: ["Mathlib"], strategy: "dense", probeBudgetMs: 30000, budgetMs: 120000 });
  console.log(`wall=${r.dt}ms`);
  console.log(r.text.split("\n").slice(0, 3).join("\n"));
  console.log("note-line:", r.text.split("\n").find((l) => l.includes("dense:")));
}
console.log("--- C: budgetMs=1500 on far_stmt (expect budget_expired, wall near budget) ---");
{
  const r = await callVerb({ filePath: CORPUS, theoremName: process.env.LEAN_LSP_BENCH_FAR ?? "far_stmt", imports: ["Mathlib"], budgetMs: 1500 });
  console.log(`wall=${r.dt}ms first-line: ${r.text.split("\n")[0]}`);
}

server.stdin.end();
setTimeout(() => process.exit(0), 1500);
