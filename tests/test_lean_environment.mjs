// Regression: root-only worker/prefix reuse survived compiler pin changes.
// All external process operations are doubled; no real LSP or compiler runs.
import assert from "node:assert/strict";
import { test, mock } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import cp from "node:child_process";
import { syncBuiltinESMExports } from "node:module";
import { EventEmitter } from "node:events";
import { PassThrough } from "node:stream";
import { FileWorkerManager, LeanSysrootBridge, McpServer } from "../src/index.ts";
import { resolveProjectRoot, planLeanInvocation } from "../src/project_root.ts";

const base = fs.mkdtempSync(path.join(os.tmpdir(), "lean-environment-"));
const previousEnv = { ...process.env };
process.env.LEAN_SHM_PATH = path.join(base, "snapshots.shm");
process.env.LEAN_SERVE_DIRECT = "1";
delete process.env.LEAN_ANALYZER_LSP;
delete process.env.LEAN_WARM_FILES;
const managers = [];
function project(name, pin = "leanprover/lean4:v4.35.0") {
  const root = path.join(base, name);
  fs.mkdirSync(root, { recursive: true });
  fs.writeFileSync(path.join(root, "lean-toolchain"), pin + "\n");
  return root;
}
function manager(root) {
  const value = new FileWorkerManager(root);
  managers.push(value);
  return value;
}
function child() {
  const value = new EventEmitter();
  value.stdout = new PassThrough();
  value.stdin = new PassThrough();
  value.exitCode = null;
  value.kill = mock.fn(() => true); // Exit can arrive AFTER replacement.
  const send = (msg) => {
    const body = JSON.stringify(msg);
    value.stdout.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
  };
  value.stdin.on("data", (bytes) => {
    const msg = JSON.parse(bytes.toString().split("\r\n\r\n")[1]);
    if (msg.id !== undefined) send({ jsonrpc: "2.0", id: msg.id, result: {} });
  });
  return { value, send };
}

try {
  await test("nested toolchain boundary resolves consistently without an outer Lake environment", () => {
    const outer = project("outer");
    fs.writeFileSync(path.join(outer, "lakefile.toml"), 'name = "outer"\n');
    const nested = project("outer/nested", "leanprover/lean4:v4.36.0-rc1");
    const deep = path.join(nested, "deep");
    fs.mkdirSync(deep);
    const resolved = resolveProjectRoot(deep, {});
    const workerRoot = manager(outer).findLeanRoot(path.join(deep, "Main.lean"));
    assert.equal(resolved.root, nested);
    assert.equal(workerRoot, resolved.root);
    assert.equal(planLeanInvocation(resolved.root, ["--stdin"]).via, "bare");
    assert.equal(resolveProjectRoot(deep, { LEAN_PROJECT_ROOT: outer }).root, outer);
  });

  await test("session pin A/B/A and late exit do not reuse or remove another environment", async () => {
    const root = project("sessions");
    fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "sessions"\n');
    const spawned = [];
    mock.method(cp, "spawn", (command, args, options) => {
      const fake = child();
      spawned.push({ ...fake, command, args, options });
      return fake.value;
    });
    syncBuiltinESMExports();
    const workers = manager(root);
    const a = await workers.ensureSession(root);
    assert.equal(await workers.ensureSession(root), a, "same environment reuses the session");
    a.diagnostics.set("file:///old.lean", { version: 1, diags: [{ message: "old" }] });
    fs.writeFileSync(path.join(root, "lean-toolchain"), "leanprover/lean4:v4.36.0-rc1\n");
    const b = await workers.ensureSession(root);
    assert.notEqual(b, a, "pin content, not just root, identifies a worker");
    assert.equal(b.diagnostics.size, 0);
    spawned[0].value.emit("exit", 0);
    assert.equal(workers.sessions.get(root), b, "late A exit must not delete B");
    spawned[0].send({ method: "textDocument/publishDiagnostics", params: { uri: "file:///old.lean", diagnostics: [{ message: "late" }] } });
    assert.equal(b.diagnostics.size, 0, "late A findings cannot enter B");
    fs.writeFileSync(path.join(root, "lean-toolchain"), "leanprover/lean4:v4.35.0\n");
    const nextA = await workers.ensureSession(root);
    assert.notEqual(nextA, a);
    assert.notEqual(nextA, b);
    assert.equal(spawned.length, 3);
    assert.equal(spawned[0].value.kill.mock.callCount(), 1);
    assert.match(workers.serverStatus(), /environment:/, "status exposes environment identity");
    mock.restoreAll(); syncBuiltinESMExports();
  });

  await test("resync caller namespaces explicit compiler and module-root changes, and missing admission is unavailable", async () => {
    const root = path.join(base, "context-session");
    fs.mkdirSync(root);
    const file = path.join(root, "Main.lean");
    fs.writeFileSync(file, "#check Nat\n");
    const contexts = ["4.35.0", "4.36.0-rc1"].map((targetVersion) => {
      const dir = path.join(base, targetVersion);
      fs.mkdirSync(dir, { recursive: true });
      const compilerPath = path.join(dir, "lean");
      fs.writeFileSync(compilerPath, "fixture", { mode: 0o755 });
      return { compilerPath, targetVersion, moduleRoots: [root] };
    });
    const spawned = [];
    mock.method(cp, "spawn", (command, args, options) => {
      const fake = child(); spawned.push({ ...fake, command, args, options }); return fake.value;
    });
    mock.method(cp, "execFileSync", (command, args) => {
      assert.deepEqual(args, ["--version"]);
      const context = contexts.find((entry) => entry.compilerPath === command);
      assert.ok(context); return `Lean (version ${context.targetVersion}, fixture)`;
    });
    mock.method(cp, "execSync", () => ""); // Existing process-table build-lock probe.
    syncBuiltinESMExports();
    const workers = manager(root);
    await assert.rejects(workers.resyncFile(file), /environment_unavailable.*standalone/);
    assert.equal(spawned.length, 0, "missing context never starts the global compiler");
    const fingerprints = [];
    for (const context of [contexts[0], contexts[1], contexts[0]]) {
      workers.setLeanContext(context);
      assert.match(await workers.resyncFile(file), /fresh didOpen/);
      const current = workers.sessions.get(root);
      fingerprints.push(current.environmentFingerprint);
      assert.equal(current.openFiles.size, 1);
      assert.equal(spawned.at(-1).command, context.compilerPath);
      assert.deepEqual(spawned.at(-1).args, ["--server"]);
      assert.equal(spawned.at(-1).options.env.LEAN_PATH, root);
    }
    assert.notEqual(fingerprints[0], fingerprints[1]);
    assert.equal(fingerprints[0], fingerprints[2], "descriptor identity is stable for A/B/A");
    const prior = workers.sessions.get(root);
    workers.setLeanContext({ ...contexts[0], moduleRoots: [] });
    await workers.resyncFile(file);
    assert.notEqual(workers.sessions.get(root), prior, "module admission changes replace worker");
    assert.equal(spawned.at(-1).options.env.LEAN_PATH, "");
    fs.mkdirSync(path.join(root, ".lake", "build"), { recursive: true });
    fs.writeFileSync(path.join(root, ".lake", "build", ".lake.lock"), "fixture");
    assert.match(await workers.resyncFile(file), /suspended during active Lake build/);
    assert.equal(spawned.length, 4, "build gate cannot be bypassed by context");
    fs.unlinkSync(path.join(root, ".lake", "build", ".lake.lock"));
    fs.writeFileSync(path.join(root, "lake.lock"), "fixture");
    await assert.rejects(workers.resyncFile(file), /environment_unavailable.*(analyzer|locked)/);
    assert.equal(spawned.length, 4, "producer lock detection also refuses uncertified context");
    mock.restoreAll(); syncBuiltinESMExports();
  });

  await test("FFI caller probes each project cwd and never caches a foreign sysroot", async () => {
    const a = project("prefix-a");
    const b = project("prefix-b", "leanprover/lean4:v4.36.0-rc1");
    const prefixA = path.join(base, "sysroot-a");
    const prefixB = path.join(base, "sysroot-b");
    for (const prefix of [prefixA, prefixB]) {
      fs.mkdirSync(path.join(prefix, "include", "lean"), { recursive: true });
      fs.writeFileSync(path.join(prefix, "include", "lean", "lean.h"), "/* fixture */\n");
    }
    const probes = [];
    const prefixFor = (cwd) => cwd === a ? prefixA : cwd === b ? prefixB : null;
    mock.method(cp, "execFileSync", (command, args, options) => {
      assert.equal(command, "lean");
      assert.deepEqual(args, ["--print-prefix"]);
      assert.ok(options.timeout > 0 && options.timeout <= 5000);
      probes.push(options.cwd);
      const prefix = prefixFor(options.cwd);
      if (!prefix) throw new Error("unavailable");
      return prefix + "\n";
    });
    // Pre-fix shell seam is doubled too: red must not spawn the host's Lean.
    mock.method(cp, "execSync", (_command, options) => prefixFor(options?.cwd) || prefixA);
    syncBuiltinESMExports();
    const servers = [new McpServer(a), new McpServer(b), new McpServer(a)];
    try {
      for (const [index, server] of servers.entries()) {
        const flags = await server.executeTool("lean_ffi", { action: "sysroot" });
        const expected = index === 1 ? prefixB : prefixA;
        const foreign = index === 1 ? prefixA : prefixB;
        assert.ok(flags.includes(`-I${expected}/include`), flags);
        assert.ok(!flags.includes(foreign), "no foreign target headers");
      }
      assert.deepEqual(probes, [a, b, a]);
      assert.deepEqual(LeanSysrootBridge.getIncludeFlags(), [], "missing root never probes the global default");
      const unavailable = LeanSysrootBridge.inspectFFI(path.join(base, "missing"));
      assert.match(unavailable, /unavailable/i);
    } finally {
      for (const server of servers) server.dispose();
      mock.restoreAll(); syncBuiltinESMExports();
    }
  });
} finally {
  for (const value of managers) value.dispose();
  mock.restoreAll(); syncBuiltinESMExports();
  for (const key of Object.keys(process.env)) if (!(key in previousEnv)) delete process.env[key];
  Object.assign(process.env, previousEnv);
  fs.rmSync(base, { recursive: true, force: true });
}
