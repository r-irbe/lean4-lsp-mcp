// tests/test_project_root.mjs
// Unit tests for src/project_root.ts and the root-scoped LakeBuildGuard check.
// Strict 7-bit ASCII only (INV-001).
//
// Regression origin: serving a `lakefile.toml`-only project (every sair contest
// lane) fell through the old `lakefile.lean`-only detector and was redirected to
// a hardcoded host path, so project modules vanished from LEAN_PATH and every
// `lean --stdin` verb answered `unknown module prefix 'Spec'`.

import assert from "node:assert";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import {
  LAKE_ROOT_MARKERS,
  explainLeanFailure,
  isLakeRoot,
  planLeanInvocation,
  resolveProjectRoot,
} from "../src/project_root.ts";
import { LakeBuildGuard } from "../src/index.ts";

console.log("=== Testing project_root + root-scoped build guard ===");

const tmpBase = fs.mkdtempSync(path.join(os.tmpdir(), "lean-root-"));

function mkProject(name, markers) {
  const dir = path.join(tmpBase, name);
  fs.mkdirSync(dir, { recursive: true });
  for (const marker of markers) {
    fs.writeFileSync(path.join(dir, marker), marker === "lean-toolchain" ? "leanprover/lean4:v4.33.1\n" : "");
  }
  return dir;
}

// 1. resolveProjectRoot
{
  // 1.1 A lakefile.toml-only root IS a root (the regression).
  const tomlOnly = mkProject("toml-only", ["lakefile.toml", "lean-toolchain"]);
  const r1 = resolveProjectRoot(tomlOnly, {});
  assert.strictEqual(r1.root, tomlOnly, "lakefile.toml-only dir resolves to itself");
  assert.strictEqual(r1.source, "cwd");
  assert.strictEqual(r1.marker, "lakefile.toml");

  // 1.2 lakefile.lean still works.
  const leanOnly = mkProject("lean-only", ["lakefile.lean"]);
  assert.strictEqual(resolveProjectRoot(leanOnly, {}).root, leanOnly);

  // 1.3 A subdirectory of a lane (e.g. <lane>/scratch) resolves to the lane.
  const lane = mkProject("lane", ["lakefile.toml", "lean-toolchain"]);
  const scratch = path.join(lane, "scratch");
  fs.mkdirSync(scratch);
  const r3 = resolveProjectRoot(scratch, {});
  assert.strictEqual(r3.root, lane, "subdirectory resolves to the enclosing Lake root");
  assert.strictEqual(r3.source, "ancestor");

  // 1.4 LEAN_PROJECT_ROOT wins (absolute, and relative-to-cwd for convenience).
  const tomlOnlyPath = path.join(tmpBase, "toml-only");
  const r4 = resolveProjectRoot(scratch, { LEAN_PROJECT_ROOT: tomlOnlyPath });
  assert.strictEqual(r4.root, tomlOnlyPath);
  assert.strictEqual(r4.source, "env");
  assert.strictEqual(resolveProjectRoot(scratch, { LEAN_PROJECT_ROOT: "../../toml-only" }).root, tomlOnlyPath);

  // 1.5 A non-existent env root is ignored (no crash, no silent wrong root).
  const r5 = resolveProjectRoot(leanOnly, { LEAN_PROJECT_ROOT: path.join(tmpBase, "nope") });
  assert.strictEqual(r5.root, leanOnly);
  assert.strictEqual(r5.source, "cwd");

  // 1.6 No marker anywhere: the cwd is returned, NOT some other project.
  const bare = path.join(tmpBase, "bare");
  fs.mkdirSync(bare, { recursive: true });
  const r6 = resolveProjectRoot(bare, {});
  assert.strictEqual(r6.root, bare, "unmarked dir stays itself (no redirection to a foreign project)");
  assert.strictEqual(r6.source, "none");
  assert.strictEqual(r6.marker, "");

  // 1.7 Toolchain-only ancestor is a last resort, not a first pick.
  const wrapper = path.join(tmpBase, "wrapper");
  fs.mkdirSync(wrapper, { recursive: true });
  fs.writeFileSync(path.join(wrapper, "lean-toolchain"), "leanprover/lean4:v4.33.1\n");
  const inside = path.join(wrapper, "deep", "dir");
  fs.mkdirSync(inside, { recursive: true });
  const r7 = resolveProjectRoot(inside, {});
  assert.strictEqual(r7.root, wrapper);
  assert.strictEqual(r7.source, "toolchain-ancestor");

  // 1.8 Marker list covers the shapes `lake new` emits.
  for (const expected of ["lakefile.lean", "lakefile.toml"]) {
    assert.ok(LAKE_ROOT_MARKERS.includes(expected), `${expected} is a lake root marker`);
  }
  assert.ok(isLakeRoot(tomlOnly) && isLakeRoot(leanOnly) && !isLakeRoot(bare));

  console.log("  - resolveProjectRoot / isLakeRoot: PASS");
}

// 2. planLeanInvocation
{
  const lakeRoot = mkProject("plan-lake", ["lakefile.toml"]);
  const inv = planLeanInvocation(lakeRoot, ["--stdin"]);
  assert.deepStrictEqual(inv, {
    command: "lake",
    args: ["env", "lean", "--stdin"],
    cwd: path.resolve(lakeRoot),
    via: "lake",
  });

  const bareRoot = path.join(tmpBase, "bare");
  const bareInv = planLeanInvocation(bareRoot, ["--stdin"]);
  assert.deepStrictEqual(bareInv, {
    command: "lean",
    args: ["--stdin"],
    cwd: path.resolve(bareRoot),
    via: "bare",
  });

  // The counterexample harness invokes a file path, not stdin.
  const fileInv = planLeanInvocation(lakeRoot, ["/tmp/x.lean"]);
  assert.deepStrictEqual(fileInv.args, ["env", "lean", "/tmp/x.lean"]);

  console.log("  - planLeanInvocation: PASS");
}

// 3. explainLeanFailure
{
  const lakeInv = planLeanInvocation(mkProject("hint-lake", ["lakefile.toml"]), ["--stdin"]);
  const hint = explainLeanFailure(
    "boot.lean:1:0: error: unknown module prefix 'Spec'\n",
    lakeInv
  );
  assert.ok(hint.includes("module 'Spec' is not on the search path"), "hint names the offending module");
  assert.ok(hint.includes("LEAN_PROJECT_ROOT"), "hint names the fix knob");
  assert.ok(hint.includes("lake env lean"), "hint shows the invocation actually used");

  const bareInv = planLeanInvocation(path.join(tmpBase, "bare"), ["--stdin"]);
  const bareHint = explainLeanFailure("error: unknown module prefix 'Spec'", bareInv);
  assert.ok(bareHint.includes("lakefile.lean / lakefile.toml / lake-manifest.json"));
  assert.ok(bareHint.includes("cannot be imported"));

  const pkgHint = explainLeanFailure("error: unknown package 'mathlib'", lakeInv);
  assert.ok(pkgHint.includes("package 'mathlib' is not in the Lake workspace"));
  assert.ok(pkgHint.includes("lake update"));

  // An ordinary elaboration error gets no hint appended.
  assert.strictEqual(explainLeanFailure("error: unsolved goals", lakeInv), "");

  console.log("  - explainLeanFailure: PASS");
}

// 4. LakeBuildGuard.isBuildOfRoot
{
  const rootA = mkProject("guard-a", ["lakefile.toml"]);
  const rootB = mkProject("guard-b", ["lakefile.toml"]);
  const lakeExe = "/home/u/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake";

  // A lake build inside the root locks it.
  assert.strictEqual(LakeBuildGuard.isBuildOfRoot(1, rootA, { exe: lakeExe, cwd: rootA }), true);
  // ... including a build in a subdirectory of the root.
  assert.strictEqual(
    LakeBuildGuard.isBuildOfRoot(1, rootA, { exe: lakeExe, cwd: path.join(rootA, "scratch") }),
    true
  );
  // A build of ANOTHER project does not (the parallel-fleet false positive).
  assert.strictEqual(LakeBuildGuard.isBuildOfRoot(1, rootB, { exe: lakeExe, cwd: rootA }), false);
  // A lake process running from a parent dir does not write our .olean tree.
  assert.strictEqual(LakeBuildGuard.isBuildOfRoot(1, rootA, { exe: lakeExe, cwd: tmpBase }), false);
  // A shell whose command line merely mentions `lake build` does not.
  assert.strictEqual(
    LakeBuildGuard.isBuildOfRoot(1, rootA, { exe: "/usr/bin/bash", cwd: rootA }),
    false
  );
  // Unreadable identity keeps the conservative answer.
  assert.strictEqual(LakeBuildGuard.isBuildOfRoot(1, rootA, null), true);

  // No lockfile + no matching process => not locked, whatever else runs on the host.
  const status = LakeBuildGuard.inspectBuildActivity(rootA);
  assert.strictEqual(status.isLocked, false, `fresh root is not locked (detail: ${status.detail || ""})`);

  console.log("  - LakeBuildGuard.isBuildOfRoot: PASS");
}

// 5. A real lockfile still trips the guard (unchanged behaviour).
{
  const rootC = mkProject("guard-c", ["lakefile.toml"]);
  fs.mkdirSync(path.join(rootC, ".lake", "build"), { recursive: true });
  fs.writeFileSync(
    path.join(rootC, ".lake", "build", ".lake.lock"),
    JSON.stringify({ pid: process.pid, lane: "test" })
  );
  const status = LakeBuildGuard.inspectBuildActivity(rootC);
  assert.strictEqual(status.isLocked, true);
  assert.strictEqual(status.source, "lockfile");
  console.log("  - lockfile detection: PASS");
}

fs.rmSync(tmpBase, { recursive: true, force: true });
console.log("=== project_root suite: ALL PASS ===");
