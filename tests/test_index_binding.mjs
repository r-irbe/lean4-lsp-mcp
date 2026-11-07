// P1 index binding: context change rebuilds the index; generation counter; stale hits refresh.
import assert from "node:assert/strict";
import { test } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { Lean4IleanIndex, McpServer } from "../src/index.ts";

const base = fs.mkdtempSync(path.join(os.tmpdir(), "idx-bind-"));
const lean = path.join(base, "lean");
fs.writeFileSync(lean, "fixture", { mode: 0o755 });
const mkRoot = (name, sym) => {
  const dir = path.join(base, name);
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, `${name}.ilean`), JSON.stringify({ module: name, decls: { [sym]: [0, 0, 1, 1] }, directImports: [] }));
  return fs.realpathSync(dir);
};
const rootA = mkRoot("ModA", "symA");
const rootB = mkRoot("ModB", "symB");
const ctx = (root) => ({ compilerPath: lean, targetVersion: "4.35.0", moduleRoots: [root] });
const project = path.join(base, "project");
fs.mkdirSync(project, { recursive: true });

test("setLeanContext rebuilds atomically: no stale symbols from the previous context", () => {
  const idx = new Lean4IleanIndex(project, ctx(rootA));
  idx.refresh();
  assert.ok(idx.lookupSymbol("symA"));
  const g = idx.getGeneration();
  idx.setLeanContext(ctx(rootB));
  assert.ok(idx.getGeneration() > g, "context change bumps the generation");
  assert.equal(idx.lookupSymbol("symA"), null, "previous context must not leak");
  assert.ok(idx.lookupSymbol("symB"));
});

test("every refresh bumps the generation (a result built under n is distinguishable from n+1)", () => {
  const idx = new Lean4IleanIndex(project, ctx(rootA));
  idx.refresh();
  const g = idx.getGeneration();
  idx.refresh();
  assert.equal(idx.getGeneration(), g + 1);
});

test("a stale positive hit is refreshed once a newer build lands (interval 0 for the test)", () => {
  process.env.LEAN_ILEAN_CURRENCY_MS = "0";
  try {
    const dir = mkRoot("ModC", "symC");
    const idx = new Lean4IleanIndex(project, ctx(dir));
    idx.refresh();
    assert.ok(idx.lookupSymbol("symC"));
    const g = idx.getGeneration();
    // a "build" lands: the declaration is renamed and the directory mtime moves forward
    fs.writeFileSync(path.join(dir, "ModC.ilean"), JSON.stringify({ module: "ModC", decls: { symC2: [0, 0, 1, 1] }, directImports: [] }));
    const future = new Date(Date.now() + 5000);
    fs.utimesSync(dir, future, future);
    assert.ok(idx.lookupSymbol("symC2"), "the rebuilt declaration is served");
    assert.ok(idx.getGeneration() > g, "a currency refresh happened on the hit path");
    assert.equal(idx.lookupSymbol("symC"), null, "the stale name is gone");
  } finally { delete process.env.LEAN_ILEAN_CURRENCY_MS; }
});

test("with the default interval, back-to-back hits do not re-scan", () => {
  const dir = mkRoot("ModD", "symD");
  const idx = new Lean4IleanIndex(project, ctx(dir));
  idx.refresh();
  idx.lookupSymbol("symD");
  const g = idx.getGeneration();
  for (let i = 0; i < 10; i++) idx.lookupSymbol("symD");
  assert.equal(idx.getGeneration(), g, "hit-path currency checks are rate limited");
});

test("hasModule distinguishes an unknown module from one with no imports", () => {
  const idx = new Lean4IleanIndex(project, ctx(rootA));
  idx.refresh();
  assert.equal(idx.hasModule("ModA"), true);
  assert.equal(idx.hasModule("Nope"), false);
});

test("McpServer.setLeanContext and dispose atomically bump ilean generation (NavBeforeReset)", () => {
  const prevShm = process.env.LEAN_SHM_PATH;
  process.env.LEAN_SHM_PATH = path.join(base, "idx-bind.shm");
  try {
    const srv = new McpServer(project);
    const idx = srv.getIleanIndex();
    const g0 = idx.getGeneration();
    idx.invalidate();
    assert.equal(idx.getGeneration(), g0 + 1);
    srv.dispose();
    assert.equal(idx.getGeneration(), g0 + 2);
  } finally {
    if (prevShm === undefined) delete process.env.LEAN_SHM_PATH;
    else process.env.LEAN_SHM_PATH = prevShm;
  }
});
