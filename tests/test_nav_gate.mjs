// P1 gate: zero spawn / execFileSync on every refusal; taxonomy; capabilities starts no session.
import assert from "node:assert/strict";
import { test, mock } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import cp from "node:child_process";
import { syncBuiltinESMExports } from "node:module";
import { McpServer } from "../src/index.ts";
import { makeFakeLsp } from "./nav_fake_lsp.mjs";

const base = fs.mkdtempSync(path.join(os.tmpdir(), "nav-gate-"));
const prevShm = process.env.LEAN_SHM_PATH;
process.env.LEAN_SHM_PATH = path.join(base, "snap.shm");
process.env.LEAN_SERVE_DIRECT = "1";
delete process.env.LEAN_NAV_REQUIRE_EXACT;

const log = { execs: [] };
mock.method(cp, "execFileSync", (command, args) => {
  log.execs.push({ command, args });
  return "Lean (version 4.35.0, fixture)";
});
mock.method(cp, "execSync", () => "");
mock.method(cp, "spawn", makeFakeLsp(log));
syncBuiltinESMExports();

function lakeProject(name) {
  const root = path.join(base, name);
  fs.mkdirSync(root, { recursive: true });
  fs.writeFileSync(path.join(root, "lakefile.toml"), "");
  fs.writeFileSync(path.join(root, "A.lean"), "def a := 1\n");
  return root;
}
function plainProject(name) {
  const root = path.join(base, name);
  fs.mkdirSync(root, { recursive: true });
  fs.writeFileSync(path.join(root, "A.lean"), "def a := 1\n");
  return root;
}
function makeCompiler(name) {
  const bin = path.join(base, name, "bin");
  fs.mkdirSync(bin, { recursive: true });
  const lean = path.join(bin, "lean");
  fs.writeFileSync(lean, "fixture", { mode: 0o755 });
  const mods = path.join(base, name, "mods");
  fs.mkdirSync(mods, { recursive: true });
  return { compilerPath: lean, targetVersion: "4.35.0", moduleRoots: [mods] };
}
const servers = [];
function server(root, ctx, opts) { const s = new McpServer(root, ctx, opts); servers.push(s); return s; }
const nav = (s, args) => s.getLakeManager().navigate(args, s.getIleanIndex());
const counts = () => ({ spawns: log.spawns.length, execs: log.execs.length });
const REFUSAL = /^environment_unavailable: (admission-missing|context-changed|live-identity-unavailable|ambiguous-warm-route|artifact-unavailable|bounds-exceeded): \w+: /;

async function refusal(promise, code) {
  await assert.rejects(promise, (e) => {
    assert.match(e.message, REFUSAL);
    assert.ok(e.message.includes(`: ${code}: `), e.message);
    assert.ok(!/not found/i.test(e.message), "a refusal must never read as 'not found'");
    return true;
  });
}

try {
  await test("no context + non-Lake root: admission-missing, zero spawn/exec", async () => {
    const root = plainProject("plain");
    const s = server(root);
    const before = counts();
    await refusal(nav(s, { operation: "hover", filePath: "A.lean", line: 1, col: 1 }), "admission-missing");
    assert.deepEqual(counts(), before);
  });

  await test("strict mode (constructor flag and env) refuses a Lake project without admission", async () => {
    const root = lakeProject("lake-strict");
    const before = counts();
    await refusal(nav(server(root, undefined, { requireExactNavigation: true }), { operation: "hover", filePath: "A.lean" }), "admission-missing");
    process.env.LEAN_NAV_REQUIRE_EXACT = "1";
    try { await refusal(nav(server(root), { operation: "hover", filePath: "A.lean" }), "admission-missing"); }
    finally { delete process.env.LEAN_NAV_REQUIRE_EXACT; }
    assert.deepEqual(counts(), before);
  });

  await test("admitted compiler replaced in place: context-changed, zero new spawn/exec", async () => {
    const root = plainProject("replaced");
    const ctx = makeCompiler("c-replaced");
    const s = server(root, ctx);
    fs.rmSync(ctx.compilerPath);
    fs.writeFileSync(ctx.compilerPath, "a-different-and-longer-binary", { mode: 0o755 });
    const before = counts();
    await refusal(nav(s, { operation: "hover", filePath: "A.lean" }), "context-changed");
    assert.deepEqual(counts(), before);
  });

  await test("lake-manifest edited after admission: context-changed, zero spawn/exec", async () => {
    const root = lakeProject("manifest");
    fs.writeFileSync(path.join(root, "lake-manifest.json"), "{}");
    const ctx = makeCompiler("c-manifest");
    const s = server(root, ctx);
    fs.writeFileSync(path.join(root, "lake-manifest.json"), '{"changed":true}');
    const before = counts();
    await refusal(nav(s, { operation: "hover", filePath: "A.lean" }), "context-changed");
    assert.deepEqual(counts(), before);
  });

  await test("capabilities introspects without starting a session", async () => {
    const s = server(plainProject("caps"));
    const before = counts();
    const out = JSON.parse(await nav(s, { operation: "capabilities" }));
    assert.ok(out.operations.includes("hover"));
    assert.ok(!out.operations.includes("rename"));
    assert.deepEqual(counts(), before);
  });

  await test("pathless operations need exactly one matching warm session", async () => {
    const root = plainProject("warm");
    const ctx = makeCompiler("c-warm");
    const s = server(root, ctx);
    const before = counts();
    await refusal(nav(s, { operation: "workspaceSymbol", query: "a" }), "live-identity-unavailable");
    assert.deepEqual(counts(), before);
    // one warm session via a path-scoped call, then pathless succeeds on it
    await nav(s, { operation: "hover", filePath: "A.lean" });
    const out = JSON.parse(await nav(s, { operation: "workspaceSymbol", query: "a" }));
    assert.equal(out.route, "live");
    assert.equal(out.contextCertified, true);
  });

  await test("validation errors are plain errors raised before any gate side effect", async () => {
    const s = server(plainProject("valid"));
    const before = counts();
    await assert.rejects(nav(s, { operation: "rename", filePath: "A.lean" }), /must be one of/);
    await assert.rejects(nav(s, { operation: "hover" }), /requires 'filePath'/);
    await assert.rejects(nav(s, { operation: "hover", filePath: "A.lean", line: 0 }), /positive integers/);
    await assert.rejects(nav(s, { operation: "codeAction", filePath: "A.lean", apply: true }), /advertise-only/);
    await assert.rejects(nav(s, { operation: "workspaceSymbol" }), /requires a non-empty 'query'/);
    assert.deepEqual(counts(), before);
  });

  await test("ambient Lake project still navigates, marked contextCertified:false", async () => {
    const root = lakeProject("ambient");
    const s = server(root);
    const out = JSON.parse(await nav(s, { operation: "hover", filePath: "A.lean", line: 1, col: 5 }));
    assert.equal(out.mode, "ambient");
    assert.equal(out.contextCertified, false);
    assert.equal(out.route, "live");
  });

  await test("wire path: a refusal is an isError result carrying the taxonomy text", async () => {
    const s = server(plainProject("wire"));
    const res = await s.handleMessage({ jsonrpc: "2.0", id: 1, method: "tools/call",
      params: { name: "lean_navigate", arguments: { operation: "hover", filePath: "A.lean" } } });
    assert.equal(res.result.isError, true);
    assert.match(res.result.content[0].text, /^Tool error: environment_unavailable: admission-missing: hover: /);
  });
} finally {
  for (const s of servers) s.dispose();
  mock.restoreAll(); syncBuiltinESMExports();
  if (prevShm === undefined) delete process.env.LEAN_SHM_PATH; else process.env.LEAN_SHM_PATH = prevShm;
  fs.rmSync(base, { recursive: true, force: true });
}
