// Fixture tests for the lean-rules declarative lint runner (22-rule O6 consolidated corpus):
// the violation fixture must trip the expected institutional rules; the clean fixture must
// produce zero findings at default warning threshold; and every *-test.yml valid/invalid case
// must match its target rule with zero regex compilation warnings.
import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import yaml from "js-yaml";
import { CliUsageError, parseArgs, runScan } from "../bin/lean-rules.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const cliPath = path.join(here, "..", "bin", "lean-rules.js");
const rulesDir = path.join(here, "..", "rules");
const violation = path.join(here, "fixtures", "rules", "violation.leanfix");
const clean = path.join(here, "fixtures", "rules", "clean.leanfix");
const ruleTestsDir = path.join(here, "fixtures", "rules", "rule-tests");

test("consolidated 22-rule corpus loads with zero compile warnings", () => {
  const { ruleCount, warnings } = runScan({ rulesDir, targets: [clean], minSeverity: "info" });
  assert.equal(ruleCount, 22, `expected the consolidated 22-rule corpus, got ${ruleCount}`);
  assert.deepEqual(warnings ?? [], [], `unexpected rule warnings: ${JSON.stringify(warnings)}`);
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

test("clean fixture produces zero findings at default warning floor", () => {
  const { findings } = runScan({ rulesDir, targets: [clean] });
  assert.equal(findings.length, 0, `clean fixture flagged: ${JSON.stringify(findings, null, 2)}`);
});

test("severity floor filters warnings", () => {
  const { findings } = runScan({ rulesDir, targets: [violation], minSeverity: "error" });
  for (const f of findings) assert.equal(f.severity, "error");
  assert.ok(findings.some((f) => f.ruleId === "rule-lean-no-sorry-cheat"));
});

test("all 7 O6 rule-test YAML suites pass valid and invalid cases (plus 500+ line proof check)", () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "lean-rule-tests-"));
  try {
    const suiteFiles = fs
      .readdirSync(ruleTestsDir)
      .filter((f) => f.endsWith(".yml"))
      .sort();
    assert.equal(suiteFiles.length, 7);

    for (const sf of suiteFiles) {
      const doc = yaml.load(fs.readFileSync(path.join(ruleTestsDir, sf), "utf-8"));
      const ruleId = doc.id;
      assert.ok(ruleId, `missing id in ${sf}`);

      for (const [idx, snippet] of (doc.valid ?? []).entries()) {
        const fp = path.join(tmp, `${sf}-valid-${idx}.leanfix`);
        fs.writeFileSync(fp, snippet);
        const { findings, warnings } = runScan({ rulesDir, targets: [fp], minSeverity: "info" });
        assert.deepEqual(warnings ?? [], [], `${sf} valid[${idx}] emitted compile warnings`);
        const hit = findings.filter((f) => f.ruleId === ruleId);
        assert.equal(
          hit.length,
          0,
          `${sf} valid[${idx}] falsely flagged ${ruleId}: ${JSON.stringify(hit)}`,
        );
      }

      for (const [idx, snippet] of (doc.invalid ?? []).entries()) {
        const fp = path.join(tmp, `${sf}-invalid-${idx}.leanfix`);
        fs.writeFileSync(fp, snippet);
        const { findings, warnings } = runScan({ rulesDir, targets: [fp], minSeverity: "info" });
        assert.deepEqual(warnings ?? [], [], `${sf} invalid[${idx}] emitted compile warnings`);
        const hit = findings.filter((f) => f.ruleId === ruleId);
        assert.ok(
          hit.length >= 1,
          `${sf} invalid[${idx}] failed to trip ${ruleId} (got: ${findings.map((f) => f.ruleId).join(", ")})`,
        );
      }
    }

    // Synthetic >500-line proof check for rule-lean-proof-length
    const longProofPath = path.join(tmp, "long-proof.leanfix");
    const bodyLines = Array.from({ length: 505 }, () => "  skip").join("\n");
    fs.writeFileSync(longProofPath, `theorem huge_proof (n : Nat) : n = n := by\n${bodyLines}\n  rfl\n`);
    const { findings } = runScan({ rulesDir, targets: [longProofPath] });
    assert.ok(
      findings.some((f) => f.ruleId === "rule-lean-proof-length"),
      "expected rule-lean-proof-length to fire on >500-line proof",
    );
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});

test("parseArgs accepts inline --flag=value, space-separated --profile sair, and rejects unknown flags", () => {
  const inline = parseArgs([
    "--profile=sair",
    "--min-severity=error",
    "--rules=/tmp/r1",
    "--config=/tmp/lean-project.toml",
    "--json",
    "Foo.lean",
  ]);
  assert.equal(inline.profile, "sair");
  assert.equal(inline.minSeverity, "error");
  assert.deepEqual(inline.rulesDirs, ["/tmp/r1"]);
  assert.equal(inline.config, "/tmp/lean-project.toml");
  assert.equal(inline.json, true);
  assert.deepEqual(inline.targets, ["Foo.lean"]);

  const spaced = parseArgs(["--profile", "all", "--", "--literal-file.lean"]);
  assert.equal(spaced.profile, "all");
  assert.deepEqual(spaced.targets, ["--literal-file.lean"]);

  assert.throws(() => parseArgs(["--unknown-flag"]), CliUsageError);
  assert.throws(() => parseArgs(["--profile=bogus"]), CliUsageError);
  assert.throws(() => parseArgs(["--profile="]), CliUsageError);
  assert.throws(() => parseArgs(["--min-severity"]), CliUsageError);
});

test("sair profile activates rule-lean-sair-submission-gate via runScan and CLI --profile=sair while default stays clean", () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "lean-sair-profile-"));
  try {
    const cleanSair = path.join(tmp, "CleanSair.leanfix");
    fs.writeFileSync(
      cleanSair,
      [
        "def impl (n : Nat) : Nat := n + 1",
        "theorem impl_correct (n : Nat) : impl n = n + 1 := by",
        "  omega",
      ].join("\n"),
    );

    const sairCases = [
      ["bv_decide.leanfix", "theorem bad_bv (x : BitVec 8) : x = x := by\n  bv_decide\n"],
      ["partial_def.leanfix", "partial def loop (n : Nat) : Nat := loop n\n"],
      ["unsafe_def.leanfix", "unsafe def rawCast (n : Nat) : Nat := n\n"],
      ["implemented_by.leanfix", "def fast (n : Nat) : Nat := n\n@[implemented_by fast]\ndef slow (n : Nat) : Nat := n\n"],
      ["extern_attr.leanfix", '@[extern "c_fn"]\nopaque extFn : Nat -> Nat\n'],
    ];

    // Auto-resolved bundled rulesDir when omitted in runScan:
    const defaultClean = runScan({ targets: [cleanSair] });
    assert.equal(defaultClean.profile, "default");
    assert.equal(defaultClean.ruleCount, 22);
    assert.equal(defaultClean.findings.length, 0);

    const sairCleanCli = spawnSync(process.execPath, [cliPath, "--profile=sair", "--json", cleanSair], {
      encoding: "utf-8",
    });
    assert.equal(sairCleanCli.status, 0, sairCleanCli.stderr);
    const sairCleanJson = JSON.parse(sairCleanCli.stdout);
    assert.equal(sairCleanJson.profile, "sair");
    assert.equal(sairCleanJson.ruleCount, 23);
    assert.equal(sairCleanJson.findings.length, 0);

    for (const [name, source] of sairCases) {
      const fp = path.join(tmp, name);
      fs.writeFileSync(fp, source);

      // Default profile leaves SAIR-only constructs unflagged:
      const defRes = runScan({ targets: [fp], profile: "default" });
      assert.equal(
        defRes.findings.filter((f) => f.ruleId === "rule-lean-sair-submission-gate").length,
        0,
        `${name} unexpectedly flagged under default profile`,
      );

      // SAIR profile flags every forbidden construct via CLI `--profile=sair`:
      const cliRes = spawnSync(process.execPath, [cliPath, "--profile=sair", "--json", fp], {
        encoding: "utf-8",
      });
      assert.equal(cliRes.status, 1, `expected exit 1 for ${name}, got ${cliRes.status}: ${cliRes.stderr}`);
      const parsed = JSON.parse(cliRes.stdout);
      assert.ok(
        parsed.findings.some((f) => f.ruleId === "rule-lean-sair-submission-gate"),
        `${name} failed to trip rule-lean-sair-submission-gate under --profile=sair`,
      );
    }

    const badFlagCli = spawnSync(process.execPath, [cliPath, "--profile=bogus", cleanSair], {
      encoding: "utf-8",
    });
    assert.equal(badFlagCli.status, 2);
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});
