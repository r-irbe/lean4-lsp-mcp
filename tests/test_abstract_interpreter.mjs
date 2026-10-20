// packages/lean-analysis/tests/test_abstract_interpreter.mjs
// Test suite for in-process abstract interpreter, sign-interval mutual reduction,
// full Nat operator transfers, and Cousot-Cousot widening/narrowing fixpoints.
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert/strict";
import {
  LeanAbstractInterpreter,
  AbstractLattice
} from "../dist/abstract_interpreter.js";

console.log("Starting Lean Abstract Interpreter Test Suite...");

// 1. Lattice operations & mutual sign-interval reduction
{
  assert.equal(AbstractLattice.join("ZERO", "POSITIVE"), "NON_NEGATIVE");
  assert.equal(AbstractLattice.join("ZERO", "NEGATIVE"), "NON_POSITIVE");
  assert.equal(AbstractLattice.join("POSITIVE", "NEGATIVE"), "TOP");
  assert.equal(AbstractLattice.join("BOTTOM", "POSITIVE"), "POSITIVE");

  assert.equal(AbstractLattice.meet("NON_NEGATIVE", "POSITIVE"), "POSITIVE");
  assert.equal(AbstractLattice.meet("NON_NEGATIVE", "ZERO"), "ZERO");
  assert.equal(AbstractLattice.meet("NON_NEGATIVE", "NEGATIVE"), "BOTTOM");

  assert.equal(AbstractLattice.isLe("ZERO", "NON_NEGATIVE"), true);
  assert.equal(AbstractLattice.isLe("POSITIVE", "NON_NEGATIVE"), true);
  assert.equal(AbstractLattice.isLe("NON_NEGATIVE", "POSITIVE"), false);

  const interp = new LeanAbstractInterpreter();
  const tightened = interp.reduceState({
    sign: "POSITIVE",
    interval: { min: 0, max: 10 },
    isDeterministic: true,
    purity: "PURE"
  });
  assert.equal(tightened.sign, "POSITIVE");
  assert.deepEqual(tightened.interval, { min: 1, max: 10 });

  const contradicted = interp.reduceState({
    sign: "POSITIVE",
    interval: { min: 0, max: 0 },
    isDeterministic: true,
    purity: "PURE"
  });
  assert.equal(contradicted.sign, "BOTTOM");
  assert.equal(contradicted.interval, undefined);

  const refinedSign = interp.reduceState({
    sign: "NON_NEGATIVE",
    interval: { min: 0, max: 0 },
    isDeterministic: true,
    purity: "PURE"
  });
  assert.equal(refinedSign.sign, "ZERO");
  assert.deepEqual(refinedSign.interval, { min: 0, max: 0 });
  console.log("  [PASS] Lattice Join, Meet, Partial Order & Mutual Sign-Interval Reduction");
}

// 2. Full Nat arithmetic expression & CST evaluation
{
  const interp = new LeanAbstractInterpreter();
  const const5 = interp.evalExpr({ value: 5 });
  assert.equal(const5.sign, "POSITIVE");
  assert.deepEqual(const5.interval, { min: 5, max: 5 });

  const const0 = interp.evalExpr({ value: 0 });
  assert.equal(const0.sign, "ZERO");

  // Nat.add
  const addExpr = interp.evalExpr({
    op: "Nat.add",
    args: [{ value: 3 }, { value: 4 }]
  });
  assert.equal(addExpr.sign, "POSITIVE");
  assert.deepEqual(addExpr.interval, { min: 7, max: 7 });

  // Nat.sub (truncating at 0)
  const subTrunc = interp.evalExpr({
    op: "Nat.sub",
    args: [{ value: 3 }, { value: 5 }]
  });
  assert.equal(subTrunc.sign, "ZERO");
  assert.deepEqual(subTrunc.interval, { min: 0, max: 0 });

  const subPos = interp.evalExpr({
    op: "Nat.sub",
    args: [{ value: 9 }, { value: 4 }]
  });
  assert.equal(subPos.sign, "POSITIVE");
  assert.deepEqual(subPos.interval, { min: 5, max: 5 });

  // Nat.mul
  const mulExpr = interp.evalExpr({
    op: "Nat.mul",
    args: [{ value: 6 }, { value: 7 }]
  });
  assert.equal(mulExpr.sign, "POSITIVE");
  assert.deepEqual(mulExpr.interval, { min: 42, max: 42 });

  // Nat.div (including total division by 0)
  const divZero = interp.evalExpr({
    op: "Nat.div",
    args: [{ value: 15 }, { value: 0 }]
  });
  assert.equal(divZero.sign, "ZERO");
  assert.deepEqual(divZero.interval, { min: 0, max: 0 });

  const divNormal = interp.evalExpr({
    op: "Nat.div",
    args: [{ value: 17 }, { value: 5 }]
  });
  assert.equal(divNormal.sign, "POSITIVE");
  assert.deepEqual(divNormal.interval, { min: 3, max: 3 });

  // Nat.mod (total mod by 0 + single-bucket exact mod)
  const modZero = interp.evalExpr({
    op: "Nat.mod",
    args: [{ value: 15 }, { value: 0 }]
  });
  assert.equal(modZero.sign, "POSITIVE");
  assert.deepEqual(modZero.interval, { min: 15, max: 15 });

  const modExpr = interp.evalExpr({
    op: "Nat.mod",
    args: [{ value: 14 }, { value: 5 }]
  });
  assert.equal(modExpr.sign, "POSITIVE");
  assert.deepEqual(modExpr.interval, { min: 4, max: 4 });

  // Nat.min & Nat.max
  const minExpr = interp.evalExpr({
    op: "Nat.min",
    args: [{ value: 12 }, { value: 5 }]
  });
  assert.deepEqual(minExpr.interval, { min: 5, max: 5 });

  const maxExpr = interp.evalExpr({
    op: "Nat.max",
    args: [{ value: 12 }, { value: 5 }]
  });
  assert.deepEqual(maxExpr.interval, { min: 12, max: 12 });

  // Tree-Sitter CST node evaluation across operators
  const cstSub = interp.evalCstNode({
    type: "apply_expression",
    children: [
      { type: "identifier", text: "Nat.sub" },
      { type: "nat_lit", text: "4" },
      { type: "nat_lit", text: "9" }
    ]
  });
  assert.equal(cstSub.sign, "ZERO");
  assert.deepEqual(cstSub.interval, { min: 0, max: 0 });

  const cstMod = interp.evalCstNode({
    type: "apply_expression",
    children: [
      { type: "identifier", text: "%" },
      { type: "nat_lit", text: "19" },
      { type: "nat_lit", text: "5" }
    ]
  });
  assert.equal(cstMod.sign, "POSITIVE");
  assert.deepEqual(cstMod.interval, { min: 4, max: 4 });

  console.log("  [PASS] Full Nat Expression & CST Abstract Evaluation");
}

// 3. Monotone Fixpoint & Cousot-Cousot Widening/Narrowing Fixpoint
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

  // Large loop bound x_{k+1} = min(x_k + 1, 1000) solved in 4 iterations via widening + narrowing
  const largeTransfer = (curr) => {
    const curMax = curr.interval ? curr.interval.max : Number.POSITIVE_INFINITY;
    const nextMax = Math.min(curMax + 1, 1000);
    return {
      sign: "NON_NEGATIVE",
      interval: { min: 0, max: nextMax },
      isDeterministic: true,
      purity: "PURE"
    };
  };

  const widenedFixpoint = interp.computeWideningFixpoint(init, largeTransfer, 5);
  assert.deepEqual(widenedFixpoint.interval, { min: 0, max: 1000 });
  assert.equal(widenedFixpoint.sign, "NON_NEGATIVE");
  console.log("  [PASS] Monotone & Widening/Narrowing Fixpoint Computation");
}

// 4. Actionable Static Diagnostic Certificates (UX Pillar 4.6)
{
  const interp = new LeanAbstractInterpreter();
  const diagSub = interp.diagnoseExpr({
    op: "Nat.sub",
    args: [{ value: 4 }, { value: 10 }]
  });
  assert.equal(diagSub.state.sign, "ZERO");
  assert.equal(diagSub.certificates.length, 1);
  assert.equal(diagSub.certificates[0].kind, "NatSubTruncation");

  const diagDivZero = interp.diagnoseExpr({
    op: "Nat.div",
    args: [{ value: 20 }, { value: 0 }]
  });
  assert.equal(diagDivZero.state.sign, "ZERO");
  assert.equal(diagDivZero.certificates.length, 1);
  assert.equal(diagDivZero.certificates[0].kind, "NatDivModByZero");
  console.log("  [PASS] Actionable Static Diagnostic Certificates");
}

// 5. Waves 2-5: Granger Interval-Congruence Reduction, Bitwise Ops, Threshold Widening & Zone Termination
{
  const interp = new LeanAbstractInterpreter();

  // Mutual Granger reduction: [1, 299] intersect (0 mod 100) -> [100, 200]
  const granger = interp.reduceState({
    sign: "NON_NEGATIVE",
    interval: { min: 1, max: 299 },
    congruence: { stride: 100, offset: 0 },
    isDeterministic: true,
    purity: "PURE"
  });
  assert.equal(granger.sign, "POSITIVE");
  assert.deepEqual(granger.interval, { min: 100, max: 200 });
  assert.deepEqual(granger.congruence, { stride: 100, offset: 0 });

  // Singleton narrowing: [95, 105] intersect (0 mod 100) -> point 100
  const grangerPoint = interp.reduceState({
    sign: "NON_NEGATIVE",
    interval: { min: 95, max: 105 },
    congruence: { stride: 100, offset: 0 },
    isDeterministic: true,
    purity: "PURE"
  });
  assert.deepEqual(grangerPoint.interval, { min: 100, max: 100 });
  assert.deepEqual(grangerPoint.congruence, { stride: 0, offset: 100 });

  // Empty intersection -> BOTTOM
  const grangerBottom = interp.reduceState({
    sign: "NON_NEGATIVE",
    interval: { min: 101, max: 199 },
    congruence: { stride: 100, offset: 0 },
    isDeterministic: true,
    purity: "PURE"
  });
  assert.equal(grangerBottom.sign, "BOTTOM");

  // Bitwise and shift evaluation
  const shlExpr = interp.evalExpr({
    op: "Nat.shiftLeft",
    args: [{ value: 5 }, { value: 2 }]
  });
  assert.deepEqual(shlExpr.interval, { min: 20, max: 20 });

  const xorExpr = interp.evalExpr({
    op: "Nat.xor",
    args: [{ value: 3 }, { value: 5 }]
  });
  assert.deepEqual(xorExpr.interval, { min: 6, max: 6 });

  // Threshold widening fixpoint stops at threshold 100
  const init0 = {
    sign: "ZERO",
    interval: { min: 0, max: 0 },
    isDeterministic: true,
    purity: "PURE"
  };
  const fpThresh = interp.computeWideningFixpoint(
    init0,
    (curr) => {
      const curMax = curr.interval ? curr.interval.max : 1000;
      const nextMax = Math.min(curMax + 1, 100);
      return {
        sign: "NON_NEGATIVE",
        interval: { min: 0, max: nextMax },
        isDeterministic: true,
        purity: "PURE"
      };
    },
    10,
    [0, 1, 50, 99, 100, 101]
  );
  assert.deepEqual(fpThresh.interval, { min: 0, max: 100 });

  // Zone DBM termination check
  assert.equal(interp.checkZoneSubDecreasing(-1, 1), "TRUE");
  assert.equal(interp.checkZoneSubDecreasing(-1, 0), "FALSE");
  assert.equal(interp.checkZoneSubDecreasing(0, 1), "TOP");
  console.log("  [PASS] Granger Reduction, Bitwise Ops, Threshold Widening & Zone Termination");
}

console.log("All Lean Abstract Interpreter tests passed 100% cleanly!");


