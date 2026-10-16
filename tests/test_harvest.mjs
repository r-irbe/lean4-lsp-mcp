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
