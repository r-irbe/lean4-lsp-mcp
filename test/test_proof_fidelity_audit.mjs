// test_proof_fidelity_audit.mjs
// Unit tests for auditLeanProofFidelity verifying 100% detection of all 7 defect patterns
// and 0 false positives on well-formed theorems.
// Strict 7-bit ASCII only (INV-001).

import { describe, it } from "node:test";
import * as assert from "node:assert/strict";
import { auditLeanProofFidelity } from "../src/proof_fidelity_audit.ts";

describe("auditLeanProofFidelity - 7 Defect Detectors & Clean Theorem Baseline", () => {
  it("detects all 7 specification and vacuity defect classes with line numbers and remediation hints", () => {
    const defectiveSource = [
      "-- 1. HYPOTHESIS_ECHO",
      "theorem defect_echo (x : Nat) (h : x > 10) : x > 10 := by",
      "  exact h",
      "",
      "-- 2. REFLEXIVE_TAUTOLOGY",
      "theorem defect_refl (a b : Nat) : a + b = a + b := by",
      "  rfl",
      "",
      "-- 3. NAT_NONNEG_TRIVIALITY",
      "theorem defect_nat_nonneg (a b : Nat) : a - b >= 0 := by",
      "  omega",
      "",
      "-- 4. NAT_SUB_UNGUARDED",
      "theorem defect_nat_sub (a b : Nat) : a - b + b = a := by",
      "  omega",
      "",
      "-- 5. UNUSED_UNDERSCORE_HYP",
      "theorem defect_unused (a : Nat) (_h : a > 0) : a + 0 = a := by",
      "  omega",
      "",
      "-- 6. MISALIGNED_DOCSTRING",
      "/-- Establishes Kuratowski planarity and Byzantine quorum safety across 8 nibbles. -/",
      "theorem defect_docstring (n : Nat) : n = n := by",
      "  rfl",
      "",
      "-- 7. ONE_WAY_BOOL_CHECKER",
      "def isPositiveNat (n : Nat) : Bool := n > 0",
      "theorem isPositiveNat_sound (n : Nat) (h : isPositiveNat n = true) : n > 0 := by",
      "  decide",
    ].join("\n");

    const report = auditLeanProofFidelity(defectiveSource);
    assert.equal(report.clean, false);
    assert.ok(report.countsByKind.HYPOTHESIS_ECHO >= 1, "Expected HYPOTHESIS_ECHO");
    assert.ok(report.countsByKind.REFLEXIVE_TAUTOLOGY >= 1, "Expected REFLEXIVE_TAUTOLOGY");
    assert.ok(report.countsByKind.NAT_NONNEG_TRIVIALITY >= 1, "Expected NAT_NONNEG_TRIVIALITY");
    assert.ok(report.countsByKind.NAT_SUB_UNGUARDED >= 1, "Expected NAT_SUB_UNGUARDED");
    assert.ok(report.countsByKind.UNUSED_UNDERSCORE_HYP >= 1, "Expected UNUSED_UNDERSCORE_HYP");
    assert.ok(report.countsByKind.MISALIGNED_DOCSTRING >= 1, "Expected MISALIGNED_DOCSTRING");
    assert.ok(report.countsByKind.ONE_WAY_BOOL_CHECKER >= 1, "Expected ONE_WAY_BOOL_CHECKER");

    for (const d of report.diagnostics) {
      assert.ok(d.line > 0, "Diagnostic must have positive 1-based line number");
      assert.ok(d.theoremName.length > 0, "Diagnostic must record theoremName");
      assert.ok(d.remediationHint.length > 0, "Diagnostic must include remediationHint");
    }
  });

  it("produces 0 false positives on well-formed theorems and bidirectional iff checkers", () => {
    const cleanSource = [
      "/-- Subtraction cancellation when guarded by `b <= a`. -/",
      "theorem sub_add_cancel_guarded (a b : Nat) (h : b <= a) : a - b + b = a := by",
      "  omega",
      "",
      "/-- Strict positivity propagation from `x > 1`. -/",
      "theorem gt_zero_of_gt_one (x : Nat) (h : x > 1) : x > 0 := by",
      "  omega",
      "",
      "def checkThreshold (n : Nat) : Bool := decide (n >= 10)",
      "",
      "/-- Necessity and sufficiency (`<->`) characterization for `checkThreshold`. -/",
      "theorem checkThreshold_iff (n : Nat) : checkThreshold n = true <-> n >= 10 := by",
      "  simp [checkThreshold]",
    ].join("\n");

    const report = auditLeanProofFidelity(cleanSource);
    assert.equal(report.clean, true, `Expected 0 diagnostics, got: ${JSON.stringify(report.diagnostics)}`);
    assert.equal(report.diagnostics.length, 0);
  });
});
