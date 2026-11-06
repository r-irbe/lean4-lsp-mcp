// Admitted-context confinement for .ilean indexing + compiler identity currency.
import assert from "node:assert/strict";
import { test } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { Lean4IleanIndex } from "../src/index.ts";
import {
  captureLeanCompilerIdentity,
  isLeanCompilerIdentityCurrent,
  leanEnvironmentFingerprint,
} from "../src/project_root.ts";

const base = fs.mkdtempSync(path.join(os.tmpdir(), "ilean-confine-"));
const writeIlean = (dir, module, sym) => {
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(path.join(dir, module + ".ilean"),
    JSON.stringify({ module, decls: { [sym]: [0, 0, 1, 1] }, directImports: [] }));
};

const project = path.join(base, "project");
const admitted = path.join(base, "admitted");
const ambient = path.join(project, ".lake", "build", "lib", "lean");
writeIlean(ambient, "Ambient", "ambientSym");
writeIlean(admitted, "Admitted", "admittedSym");
const outside = path.join(base, "outside");
writeIlean(outside, "Escaped", "escapedSym");
fs.symlinkSync(path.join(outside, "Escaped.ilean"), path.join(admitted, "Escaped.ilean"));
fs.mkdirSync(path.join(base, "bin"), { recursive: true });
const lean = path.join(base, "bin", "lean");
fs.writeFileSync(lean, "fixture", { mode: 0o755 });
const ctx = { compilerPath: lean, targetVersion: "4.35.0", moduleRoots: [fs.realpathSync(admitted)] };

test("admitted context sees only moduleRoots; ambient and symlink-escaped ileans are ignored", () => {
  const idx = new Lean4IleanIndex(project, ctx);
  idx.refresh();
  assert.ok(idx.lookupSymbol("admittedSym"));
  assert.equal(idx.lookupSymbol("ambientSym"), null);
  assert.equal(idx.lookupSymbol("escapedSym"), null);
});

test("negative control: without a context the ambient build tree is indexed", () => {
  const idx = new Lean4IleanIndex(project);
  idx.refresh();
  assert.ok(idx.lookupSymbol("ambientSym"));
});

test("compiler replacement and manifest edits change the fingerprint; symlinks fail identity", () => {
  const manifest = path.join(project, "lake-manifest.json");
  fs.writeFileSync(manifest, "{}");
  const fp1 = leanEnvironmentFingerprint(project, lean, [], process.env, ctx);
  const id = captureLeanCompilerIdentity(lean);
  assert.ok(isLeanCompilerIdentityCurrent(lean, id));
  fs.writeFileSync(manifest, '{"v":2}');
  assert.notEqual(leanEnvironmentFingerprint(project, lean, [], process.env, ctx), fp1);
  fs.rmSync(lean);
  fs.writeFileSync(lean, "replaced-longer", { mode: 0o755 });
  assert.equal(isLeanCompilerIdentityCurrent(lean, id), false);
  const link = path.join(base, "bin", "lean-link");
  fs.symlinkSync(lean, link);
  assert.equal(isLeanCompilerIdentityCurrent(link, captureLeanCompilerIdentity(link)), false);
});

// ---- item 3: runBoundedLean and resolveSymbol honour the admitted context ----
import { McpServer, LeanSysrootBridge } from "../src/index.ts";

test("runBoundedLean executes the admitted compiler with admitted LEAN_PATH, never ambient lake", async () => {
  const root = path.join(base, "bounded-root");
  fs.mkdirSync(root, { recursive: true });
  fs.writeFileSync(path.join(root, "lakefile.toml"), "");
  const prefix = path.join(base, "bounded-prefix", "bin");
  fs.mkdirSync(prefix, { recursive: true });
  const fake = path.join(prefix, "lean");
  fs.writeFileSync(fake, '#!/bin/sh\nif [ "$1" = "--version" ]; then echo "Lean (version 4.35.0, x86_64)"; exit 0; fi\necho "RAN:$LEAN_PATH"\n', { mode: 0o755 });
  const bctx = { compilerPath: fake, targetVersion: "4.35.0", moduleRoots: [fs.realpathSync(admitted)] };
  const server = new McpServer(root, bctx);
  const run = await server.runBoundedLean(path.join(root, "x.lean"), 5000);
  assert.equal(run.exitCode, 0, run.output);
  assert.match(run.output, new RegExp("RAN:" + fs.realpathSync(admitted)));
  // wrong declared version fails closed before any source executes
  const wrong = new McpServer(root, { ...bctx, targetVersion: "4.36.0" });
  const bad = await wrong.runBoundedLean(path.join(root, "x.lean"), 5000);
  assert.equal(bad.exitCode, null);
  assert.match(bad.output, /environment_unavailable/);
});

test("resolveSymbol scans admitted module roots outside the project", () => {
  const roots = path.join(base, "ffi-proj");
  fs.mkdirSync(roots, { recursive: true });
  const mod = path.join(base, "ffi-mods");
  fs.mkdirSync(mod, { recursive: true });
  fs.writeFileSync(path.join(mod, "Ext.lean"), '@[extern "my_c_sym"] opaque f : Nat\n');
  const fctx = { compilerPath: lean, targetVersion: "4.35.0", moduleRoots: [fs.realpathSync(mod)] };
  const withCtx = LeanSysrootBridge.resolveSymbol(roots, "my_c_sym", fctx);
  assert.equal(withCtx.leanToC.length, 1);
  assert.equal(LeanSysrootBridge.resolveSymbol(roots, "my_c_sym").leanToC.length, 0);
});

// ---- elan shim support and cap reporting ----
import { validateLeanContext, resolveElanShim } from "../src/project_root.ts";

function fakeElan(name) {
  const home = path.join(base, name);
  fs.mkdirSync(path.join(home, "bin"), { recursive: true });
  fs.writeFileSync(path.join(home, "bin", "elan"), "elan-multiplexer", { mode: 0o755 });
  fs.symlinkSync(path.join(home, "bin", "elan"), path.join(home, "bin", "lean"));
  const tcBin = path.join(home, "toolchains", "leanprover--lean4---v4.35.0", "bin");
  fs.mkdirSync(tcBin, { recursive: true });
  fs.writeFileSync(path.join(tcBin, "lean"), "real-lean", { mode: 0o755 });
  return { home, shim: path.join(home, "bin", "lean"), real: fs.realpathSync(path.join(tcBin, "lean")) };
}

test("elan shim resolves to the exact direct toolchain binary for targetVersion", () => {
  const e = fakeElan("elan-a");
  const admittedCtx = validateLeanContext({ compilerPath: e.shim, targetVersion: "4.35.0", moduleRoots: [admitted] });
  assert.equal(admittedCtx.compilerPath, e.real);
  // idempotent: the resolved context re-admits unchanged
  assert.deepEqual(validateLeanContext(admittedCtx), admittedCtx);
});

test("shim for a version with no installed toolchain, or a non-elan symlink, stays refused", () => {
  const e = fakeElan("elan-b");
  assert.equal(resolveElanShim(e.shim, "4.99.0"), undefined);
  assert.throws(() => validateLeanContext({ compilerPath: e.shim, targetVersion: "4.99.0", moduleRoots: [admitted] }), /unavailable|symlink|elan shim cannot be admitted/);
  const plain = path.join(base, "plain-target");
  fs.writeFileSync(plain, "x", { mode: 0o755 });
  const link = path.join(base, "plain-link", "lean");
  fs.mkdirSync(path.dirname(link), { recursive: true });
  fs.symlinkSync(plain, link);
  assert.equal(resolveElanShim(link, "4.35.0"), undefined);
  assert.throws(() => validateLeanContext({ compilerPath: link, targetVersion: "4.35.0", moduleRoots: [admitted] }), /symlink.*unsupported/);
});

test("a symlinked toolchain binary behind the shim is refused (no swap via toolchain symlink)", () => {
  const e = fakeElan("elan-c");
  const tc = path.join(e.home, "toolchains", "leanprover--lean4---v4.35.0", "bin", "lean");
  fs.rmSync(tc);
  fs.symlinkSync(path.join(base, "plain-target"), tc);
  assert.equal(resolveElanShim(e.shim, "4.35.0"), undefined);
});

test("file cap is env-tunable and skips are reported, not silent", () => {
  const dir = path.join(base, "many");
  for (let i = 0; i < 5; i++) writeIlean(dir, `M${i}`, `sym${i}`);
  const mctx = { compilerPath: lean, targetVersion: "4.35.0", moduleRoots: [fs.realpathSync(dir)] };
  process.env.LEAN_ILEAN_MAX_FILES = "2";
  try {
    const idx = new Lean4IleanIndex(project, mctx);
    idx.refresh();
    const report = idx.getScanReport();
    assert.equal(report.scannedFiles, 2);
    assert.equal(report.skipped.overFileCap, 3);
  } finally { delete process.env.LEAN_ILEAN_MAX_FILES; }
  const full = new Lean4IleanIndex(project, mctx);
  full.refresh();
  assert.equal(full.getScanReport().scannedFiles, 5);
});

test("hardlinked elan shim (what elan really installs) resolves, or is refused when the toolchain is absent", () => {
  const e = fakeElan("elan-hard");
  fs.rmSync(e.shim);
  fs.linkSync(path.join(e.home, "bin", "elan"), e.shim); // same dev+ino as elan
  const ctx1 = validateLeanContext({ compilerPath: e.shim, targetVersion: "4.35.0", moduleRoots: [admitted] });
  assert.equal(ctx1.compilerPath, e.real);
  // must NOT silently admit the shim itself as a "direct" compiler
  assert.throws(
    () => validateLeanContext({ compilerPath: e.shim, targetVersion: "4.99.0", moduleRoots: [admitted] }),
    /elan shim cannot be admitted/,
  );
});

test("default file cap covers the largest known Lean trees (Mathlib+deps+toolchain ~11.6k)", () => {
  delete process.env.LEAN_ILEAN_MAX_FILES;
  assert.ok(Lean4IleanIndex.maxIleanFiles() >= 4 * 11_600);
  process.env.LEAN_ILEAN_MAX_FILES = "garbage";
  try { assert.equal(Lean4IleanIndex.maxIleanFiles(), 65536); } finally { delete process.env.LEAN_ILEAN_MAX_FILES; }
});
