// Explicit compiler context must reach actual MCP execution, not just a planner.
// Process-boundary doubles attest no real compiler/LSP or project code runs.
import assert from "node:assert/strict";
import { test, mock } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import cp from "node:child_process";
import { syncBuiltinESMExports } from "node:module";
import { McpServer, TOOL_DEFINITIONS } from "../src/index.ts";
import { planLeanInvocation } from "../src/project_root.ts";

const base = fs.mkdtempSync(path.join(os.tmpdir(), "lean-context-"));
const before = { ...process.env };
process.env.LEAN_SHM_PATH = path.join(base, "snapshots.shm");
process.env.LEAN_PATH = path.join(base, "foreign-global-root");
process.env.LEAN_SYSROOT = path.join(base, "foreign-global-sysroot");
const root = path.join(base, "standalone");
const modules = path.join(root, "admitted-modules");
fs.mkdirSync(modules, { recursive: true });
fs.writeFileSync(path.join(modules, "Helper.olean"), "fixture, not loaded by a real compiler");
function context(version) {
  const prefix = path.join(base, version);
  fs.mkdirSync(path.join(prefix, "bin"), { recursive: true });
  fs.mkdirSync(path.join(prefix, "include", "lean"), { recursive: true });
  fs.writeFileSync(path.join(prefix, "bin", "lean"), "fixture", { mode: 0o755 });
  fs.writeFileSync(path.join(prefix, "include", "lean", "lean.h"), "/* fixture */");
  return { compilerPath: path.join(prefix, "bin", "lean"), targetVersion: version, moduleRoots: [modules] };
}
const a = context("4.35.0");
const b = context("4.36.0-rc1");
const calls = [];
mock.method(cp, "execFileSync", (command, args, options) => {
  calls.push({ command, args, options });
  const ctx = command === a.compilerPath ? a : command === b.compilerPath ? b : null;
  assert.ok(ctx, "only explicitly selected compiler is run");
  assert.equal(options.cwd, root);
  assert.ok(options.timeout > 0 && options.maxBuffer > 0);
  assert.equal(options.env.LEAN_PATH, modules, "global roots are replaced, not appended");
  assert.equal(options.env.LEAN_SYSROOT, undefined);
  if (args[0] === "--version") return `Lean (version ${ctx.targetVersion}, fixture)\n`;
  if (args[0] === "--print-prefix") return path.dirname(path.dirname(command)) + "\n";
  assert.deepEqual(args, ["--stdin"]);
  if (options.input.includes("BAD_SOURCE")) {
    const err = new Error("compiler exited 1");
    err.stdout = "Main.lean:2:0: error: type mismatch";
    throw err;
  }
  if (options.input.includes("MISSING_MODULE")) {
    const err = new Error("compiler exited 1");
    err.stdout = "Main.lean:1:0: error: unknown module prefix 'Missing'";
    throw err;
  }
  return `checked with ${ctx.targetVersion}`;
});
// Pre-fix execution is doubled: it should expose the wrong default, not run Lean.
mock.method(cp, "execSync", () => "global Lean 4.33.1: unknown module prefix 'Helper'");
syncBuiltinESMExports();
const server = new McpServer(root);
try {
  await test("lean_exec exact A/B/A context admits standalone modules without global LEAN_PATH", async () => {
    for (const ctx of [a, b, a]) {
      const output = await server.executeTool("lean_exec", { code: "import Helper", context: ctx });
      assert.equal(output, `checked with ${ctx.targetVersion}`);
    }
    assert.deepEqual(calls.filter((call) => call.args[0] === "--stdin").map((call) => call.command), [a.compilerPath, b.compilerPath, a.compilerPath]);
    const plan = planLeanInvocation(root, ["--stdin"], a);
    assert.equal(plan.command, a.compilerPath);
    assert.deepEqual(plan.args, ["--stdin"]);
    assert.equal(plan.env.LEAN_PATH, modules);
    assert.ok(!JSON.stringify(plan).includes("foreign-global"));
  });

  await test("declared wrong version is environment-unavailable before source execution", async () => {
    const priorSourceCalls = calls.filter((call) => call.args[0] === "--stdin").length;
    const output = await server.executeTool("lean_exec", { code: "BAD_SOURCE", context: { ...a, targetVersion: b.targetVersion } });
    assert.match(output, /environment_unavailable/);
    assert.match(output, /4\.36\.0-rc1.*4\.35\.0/);
    assert.equal(calls.filter((call) => call.args[0] === "--stdin").length, priorSourceCalls);
  });

  await test("matching context preserves source errors and contextual missing-module hints", async () => {
    const output = await server.executeTool("lean_exec", { code: "BAD_SOURCE", context: a });
    assert.match(output, /type mismatch/);
    assert.ok(!output.includes("environment_unavailable"));
    const missing = await server.executeTool("lean_exec", { code: "MISSING_MODULE", context: a });
    assert.match(missing, /unknown module prefix 'Missing'/);
    assert.match(missing, /explicitly admitted module roots/);
    assert.ok(!missing.includes("project modules cannot be imported"));
  });

  await test("context validation rejects arbitrary command/env, relative roots, absent compiler and invalid target", async () => {
    const canonicalInvalidRoot = path.join(base, `modules${path.delimiter}extra`);
    const moduleAlias = path.join(base, "module-alias");
    fs.mkdirSync(canonicalInvalidRoot);
    fs.symlinkSync(canonicalInvalidRoot, moduleAlias, "dir");
    for (const invalid of [
      { ...a, command: "sh" }, { ...a, env: { LEAN_PATH: "/anywhere" } },
      { ...a, compilerPath: "lean" }, { ...a, compilerPath: path.join(base, "missing", "lean") },
      { ...a, compilerPath: path.join(base, "sh") },
      { ...a, moduleRoots: ["relative"] }, { ...a, moduleRoots: [path.join(base, "missing")] },
      { ...a, targetVersion: "latest" }, { ...a, targetVersion: "4.35.0; echo bad" },
      { ...a, moduleRoots: "not-an-array" },
      { ...a, moduleRoots: [modules + path.delimiter + root] },
      { ...a, moduleRoots: [moduleAlias] },
    ]) {
      await assert.rejects(server.executeTool("lean_exec", { code: "#check Nat", context: invalid }), /Invalid Lean context/);
    }
  });

  await test("lean_ffi actual caller uses exact target context and reports missing runtime headers", async () => {
    for (const ctx of [a, b, a]) {
      const hostAdmitted = new McpServer(root, ctx);
      try {
        const output = await hostAdmitted.executeTool("lean_ffi", { action: "sysroot", context: ctx });
        assert.ok(output.includes(path.join(path.dirname(path.dirname(ctx.compilerPath)), "include")), output);
      } finally { hostAdmitted.dispose(); }
    }
    fs.unlinkSync(path.join(base, "4.36.0-rc1", "include", "lean", "lean.h"));
    const hostAdmitted = new McpServer(root, b);
    try {
      const output = await hostAdmitted.executeTool("lean_ffi", { action: "sysroot", context: b });
      assert.match(output, /environment_unavailable/);
    } finally { hostAdmitted.dispose(); }
  });

  await test("optional context schema does not change existing required tool arguments", () => {
    for (const name of ["lean_exec", "lean_ffi"]) {
      const schema = TOOL_DEFINITIONS.find((tool) => tool.name === name).inputSchema;
      assert.equal(schema.properties.context.type, "object");
      assert.equal(schema.properties.context.additionalProperties, false);
      assert.ok(!schema.required?.includes("context"));
    }
  });
} finally {
  server.dispose();
  mock.restoreAll(); syncBuiltinESMExports();
  for (const key of Object.keys(process.env)) if (!(key in before)) delete process.env[key];
  Object.assign(process.env, before);
  fs.rmSync(base, { recursive: true, force: true });
}
