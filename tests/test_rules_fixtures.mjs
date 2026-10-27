// Fixture tests for the lean-rules declarative lint runner (W2 of the
// lean-analysis packaging plan): the violation fixture must trip exactly the
// expected institutional rules; the clean fixture must produce zero findings.
import test from "node:test";
import assert from "node:assert/strict";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { runScan } from "../bin/lean-rules.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const rulesDir = path.join(here, "..", "rules");
const violation = path.join(here, "fixtures", "rules", "violation.leanfix");
const clean = path.join(here, "fixtures", "rules", "clean.leanfix");

test("rule corpus loads", () => {
  const { ruleCount } = runScan({ rulesDir, targets: [clean] });
  assert.equal(ruleCount, 16, `expected the consolidated 16-rule corpus, got ${ruleCount}`);
});

test("violation fixture trips the expected rule ids", () => {
  const { findings } = runScan({ rulesDir, targets: [violation] });
  const ids = new Set(findings.map((f) => f.ruleId));
  for (const expected of [
    "rule-lean-no-sorry-cheat",
    "rule-lean-no-uncertified-axiom",
    "rule-lean-no-redundant-idempotent-tactic",
    "rule-lean-no-unbounded-heartbeats",
    "rule-lean-max-import-depth",
  ]) {
    assert.ok(ids.has(expected), `missing finding: ${expected} (got: ${[...ids].join(", ")})`);
  }
  for (const f of findings) {
    assert.ok(f.file.endsWith("violation.leanfix"), `finding leaked to another file: ${f.file}`);
  }
  const sorry = findings.find((f) => f.ruleId === "rule-lean-no-sorry-cheat");
  assert.equal(sorry.severity, "error");
});

test("clean fixture produces zero findings", () => {
  const { findings } = runScan({ rulesDir, targets: [clean] });
  assert.equal(findings.length, 0, `clean fixture flagged: ${JSON.stringify(findings, null, 2)}`);
});

test("severity floor filters warnings", () => {
  const { findings } = runScan({ rulesDir, targets: [violation], minSeverity: "error" });
  for (const f of findings) assert.equal(f.severity, "error");
  assert.ok(findings.some((f) => f.ruleId === "rule-lean-no-sorry-cheat"));
});
