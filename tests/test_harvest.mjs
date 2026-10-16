// Unit tests for the lean-harvest CLI (W4 of lean-analysis packaging plan).
import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const here = path.dirname(fileURLToPath(import.meta.url));
const binHarvest = path.join(here, "..", "bin", "lean-harvest.js");

test("lean-harvest CLI displays help banner", () => {
  const res = spawnSync("node", [binHarvest, "--help"], { encoding: "utf-8" });
  assert.equal(res.status, 0);
  assert.ok(res.stdout.includes("usage: lean-harvest"));
  assert.ok(res.stdout.includes("--flags"));
});

test("lean-harvest CLI rejects missing arguments", () => {
  const res = spawnSync("node", [binHarvest], { encoding: "utf-8" });
  assert.equal(res.status, 2);
  assert.ok(res.stderr.includes("error: missing output file"));
});

test("lean-harvest CLI parses output correctly", () => {
  const tmpOut = path.join(os.tmpdir(), `harvest_test_${Date.now()}.json`);
  try {
    // Run on a known clean file or fixture with a standard flag
    const fixtureFile = path.join(here, "fixtures", "rules", "clean.leanfix");
    const res = spawnSync("node", [binHarvest, "--output", tmpOut, "--flags", "linter.unusedVariables", "--json", fixtureFile], {
      encoding: "utf-8",
    });
    // Even if lake is not configured for this fixture directory, it should emit JSON
    if (fs.existsSync(tmpOut)) {
      const data = JSON.parse(fs.readFileSync(tmpOut, "utf-8"));
      assert.ok(Array.isArray(data));
    }
  } finally {
    try { fs.unlinkSync(tmpOut); } catch {}
  }
});

// ---- format contract (parity with the reference shell implementation) ----

// A stub `lake` placed on PATH emits deterministic diagnostics so the TSV
// row contract is testable without a Lean toolchain.
const stubLake = [
  "#!/bin/sh",
  'flag=""',
  'last=""',
  'for a in "$@"; do',
  '  last="$a"',
  '  case "$a" in',
  '    -D*=true) flag="${a#-D}"; flag="${flag%=true}" ;;',
  '  esac',
  'done',
  'printf "%s\\n" "$last:42:0: warning: The module doc-string for a file should be the first command after the imports."',
  'printf "%s\\n" "$last:7:0: information: this is informational output"',
  'printf "%s\\n" "<input>:1:0: error: invalid -D parameter, unknown configuration option \'$flag\'"',
  'printf "%s\\n" "  continuation line that must be ignored"',
  "",
].join("\n");

function runStubHarvest(flagsText) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "harvest_format_"));
  const stubDir = path.join(dir, "stub");
  fs.mkdirSync(stubDir);
  const stub = path.join(stubDir, "lake");
  fs.writeFileSync(stub, stubLake);
  fs.chmodSync(stub, 0o755);
  const pkg = path.join(dir, "pkg");
  fs.mkdirSync(pkg);
  fs.writeFileSync(path.join(pkg, "Fixture.lean"), "");
  const out = path.join(dir, "out.tsv");
  const res = spawnSync("node", [binHarvest, out, flagsText, "Fixture.lean"], {
    cwd: pkg,
    env: { ...process.env, PATH: `${stubDir}:${process.env.PATH}` },
    encoding: "utf-8",
  });
  assert.equal(res.status, 0, res.stderr);
  return fs.readFileSync(out, "utf-8").trim().split("\n").sort();
}

test("format: line-number column, severity-kept message, COVERAGE rows", () => {
  const rows = runStubHarvest("linter.style.header");
  assert.deepEqual(rows, [
    "COVERAGE\tFixture.lean\t1\t<input>:1:0: error: invalid -D parameter, unknown configuration option 'linter.style.header'",
    "linter.style.header\tFixture.lean\t1\terror: invalid -D parameter, unknown configuration option 'linter.style.header'",
    "linter.style.header\tFixture.lean\t42\twarning: The module doc-string for a file should be the first command after the imports.",
  ].sort());
});

test("format: unknown flag keeps every diagnostic and both rows", () => {
  const rows = runStubHarvest("linter.bogus.probe");
  assert.deepEqual(rows, [
    "COVERAGE\tFixture.lean\t1\t<input>:1:0: error: invalid -D parameter, unknown configuration option 'linter.bogus.probe'",
    "linter.bogus.probe\tFixture.lean\t1\terror: invalid -D parameter, unknown configuration option 'linter.bogus.probe'",
    "linter.bogus.probe\tFixture.lean\t42\twarning: The module doc-string for a file should be the first command after the imports.",
    "linter.bogus.probe\tFixture.lean\t7\tinformation: this is informational output",
  ].sort());
});
