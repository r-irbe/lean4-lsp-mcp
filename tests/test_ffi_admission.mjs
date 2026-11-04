// Review 831: inspection never admits a caller-selected executable.
import assert from "node:assert/strict";
import { test, mock } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import cp from "node:child_process";
import { syncBuiltinESMExports } from "node:module";
import { McpServer, FileWorkerManager } from "../src/index.ts";
import { validateLeanContext } from "../src/project_root.ts";

const root = fs.mkdtempSync(path.join(os.tmpdir(), "ffi-admission-"));
const previousShm = process.env.LEAN_SHM_PATH;
process.env.LEAN_SHM_PATH = path.join(root, "snapshots.shm");
const compilerPath = path.join(root, "lean");
fs.writeFileSync(compilerPath, "#!/bin/sh\nexit 99\n", { mode: 0o755 });
fs.mkdirSync(path.join(root, "include", "lean"), { recursive: true });
fs.writeFileSync(path.join(root, "include", "lean", "lean.h"), "/* fixture */");
const context = { compilerPath, targetVersion: "4.35.0", moduleRoots: [root] };
const calls = [];
mock.method(cp, "execFileSync", (command, args) => {
  calls.push({ command, args });
  return args[0] === "--version" ? "Lean (version 4.35.0, fixture)" : args[0] === "--stdin" ? "privileged exec" : root;
});
mock.method(cp, "execSync", () => "");
mock.method(cp, "spawn", () => { throw new Error("unexpected worker spawn"); });
syncBuiltinESMExports();
const servers = [];
function server(admitted) { const value = new McpServer(root, admitted); servers.push(value); return value; }
function wire(value, name, args) { return value.handleMessage({ jsonrpc: "2.0", id: 1, method: "tools/call", params: { name, arguments: args } }); }
try {
  await test("wire FFI rejects project executable before any probe without host admission", async () => {
    const value = server();
    for (const name of ["lean_ffi", "lean_c_ffi_inspect", "lean_c_ffi"]) {
      const before = calls.length;
      const result = await wire(value, name, { action: "sysroot", context });
      assert.equal(calls.length, before, "even --version must not invoke the project executable");
      assert.equal(result.result.isError, true);
      assert.match(result.result.content[0].text, /host.*admi/);
    }
  });
  await test("wire FFI uses only exact constructor-admitted context, distinct from exec privilege", async () => {
    const value = server(context);
    const allowed = await wire(value, "lean_ffi", { action: "sysroot", context });
    assert.ok(!allowed.result.isError);
    assert.match(allowed.result.content[0].text, /-I/);
    const before = calls.length;
    const denied = await wire(value, "lean_ffi", { action: "sysroot", context: { ...context, moduleRoots: [] } });
    assert.equal(denied.result.isError, true);
    assert.equal(calls.length, before);
    const exec = await wire(server(), "lean_exec", { code: "#check Nat", context });
    assert.equal(exec.result.content[0].text, "privileged exec");
  });
  await test("compiler admission is idempotent and rejects argv0-changing symlinks at first admission", async () => {
    assert.deepEqual(validateLeanContext(validateLeanContext(context)), validateLeanContext(context));
    const dir = path.join(root, "alias"); fs.mkdirSync(dir);
    const target = path.join(dir, "lean-real"); fs.writeFileSync(target, "fixture", { mode: 0o755 });
    const alias = path.join(dir, "lean"); fs.symlinkSync(target, alias);
    const input = { ...context, compilerPath: alias };
    assert.throws(() => validateLeanContext(input), /symlink.*unsupported/);
    assert.throws(() => new McpServer(root, input), /symlink.*unsupported/);
    const before = calls.length;
    for (const [value, name] of [[server(), "lean_exec"], [server(context), "lean_ffi"]]) {
      const result = await wire(value, name, { code: "#check Nat", action: "sysroot", context: input });
      assert.equal(result.result.isError, true);
      assert.match(result.result.content[0].text, /symlink.*unsupported/);
    }
    const workers = new FileWorkerManager(root);
    try { assert.throws(() => workers.setLeanContext(input), /symlink.*unsupported/); }
    finally { workers.dispose(); }
    assert.equal(calls.length, before, "unsupported compiler alias is rejected before any execution");
  });
} finally {
  for (const value of servers) value.dispose();
  mock.restoreAll(); syncBuiltinESMExports();
  if (previousShm === undefined) delete process.env.LEAN_SHM_PATH; else process.env.LEAN_SHM_PATH = previousShm;
  fs.rmSync(root, { recursive: true, force: true });
}
