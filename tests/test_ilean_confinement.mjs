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
