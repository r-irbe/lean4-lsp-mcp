// packages/lean-analysis/tests/test_abstract_interpreter.mjs
// Test suite for in-process abstract interpreter and lattice operations
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert/strict";
import {
  LeanAbstractInterpreter,
  AbstractLattice
} from "../dist/abstract_interpreter.js";

console.log("Starting Lean Abstract Interpreter Test Suite...");

// 1. Lattice operations
{
  assert.equal(AbstractLattice.join("ZERO", "POSITIVE"), "NON_NEGATIVE");
  assert.equal(AbstractLattice.join("ZERO", "NEGATIVE"), "NON_POSITIVE");
  assert.equal(AbstractLattice.join("POSITIVE", "NEGATIVE"), "TOP");
  assert.equal(AbstractLattice.join("BOTTOM", "POSITIVE"), "POSITIVE");

  assert.equal(AbstractLattice.meet("NON_NEGATIVE", "POSITIVE"), "POSITIVE");
  assert.equal(AbstractLattice.meet("NON_NEGATIVE", "ZERO"), "ZERO");
  assert.equal(AbstractLattice.meet("NON_NEGATIVE", "NEGATIVE"), "BOTTOM");
  console.log("  [PASS] Lattice Join and Meet Operations");
}

// 2. Arithmetic expression evaluation
{
  const interp = new LeanAbstractInterpreter();
  const const5 = interp.evalExpr({ value: 5 });
  assert.equal(const5.sign, "POSITIVE");
  assert.deepEqual(const5.interval, { min: 5, max: 5 });

  const const0 = interp.evalExpr({ value: 0 });
  assert.equal(const0.sign, "ZERO");

  const addExpr = interp.evalExpr({
    op: "Nat.add",
    args: [{ value: 3 }, { value: 4 }]
  });
  assert.equal(addExpr.sign, "POSITIVE");
  assert.deepEqual(addExpr.interval, { min: 7, max: 7 });
  console.log("  [PASS] Expression Abstract Evaluation");
}

// 3. Fixpoint calculation
{
  const interp = new LeanAbstractInterpreter();
  const init = {
    sign: "ZERO",
    interval: { min: 0, max: 0 },
    isDeterministic: true,
    purity: "PURE"
  };

  // Transfer function: x_{k+1} = min(x_k + 1, 10)
  const transfer = (curr) => {
    const curMax = curr.interval ? curr.interval.max : 0;
    const nextMax = Math.min(curMax + 1, 10);
    return {
      sign: nextMax > 0 ? "POSITIVE" : "ZERO",
      interval: { min: 0, max: nextMax },
      isDeterministic: true,
      purity: "PURE"
    };
  };

  const fixpoint = interp.computeFixpoint(init, transfer, 25);
  assert.equal(fixpoint.interval.max, 10);
  assert.equal(fixpoint.sign, "NON_NEGATIVE");
  console.log("  [PASS] Abstract State Fixpoint Computation");
}

console.log("All Lean Abstract Interpreter tests passed 100% cleanly!");
