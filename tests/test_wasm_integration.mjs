// packages/lean-analysis/tests/test_wasm_integration.mjs
// Verifies real WASM engine integration with packages/lean-analysis
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { LeanAbstractInterpreter, diagnoseLeanSourceWasm } from "../src/abstract_interpreter.ts";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

console.log("Starting Real Lean WASM Engine Integration Test...");

const wasmPath = path.resolve(__dirname, "../data/lean_analyzer.wasm");
assert.ok(fs.existsSync(wasmPath), `WASM binary missing at ${wasmPath}`);

const wasmBytes = fs.readFileSync(wasmPath);
assert.ok(wasmBytes.length > 0 && wasmBytes.length <= 131072, `WASM binary size ${wasmBytes.length} outside (0, 131072]`);
console.log(`  [INFO] Loaded lean_analyzer.wasm (${wasmBytes.length} bytes)`);

const interp = new LeanAbstractInterpreter();
assert.equal(interp.isUsingWasm(), true, "Expected default LeanAbstractInterpreter() to auto-load WASM engine");
const synthDefault = interp.synthesizeTerminationDecreasingBy(-1, 1);
assert.equal(synthDefault.decreasingBy, "by omega");
assert.deepEqual(synthDefault.alternatives, ["by omega"]);
const synthCustom = interp.synthesizeTerminationDecreasingBy(-1, 1, { enableCustomProjectTactics: true });
assert.deepEqual(synthCustom.alternatives, ["by omega", "by scaled_omega"]);

const loaded = await interp.loadWasmEngine(new Uint8Array(wasmBytes));
assert.equal(loaded, true, "Failed to instantiate WebAssembly engine");

// Directly test exported WASM functions
const wasmModule = await WebAssembly.instantiate(wasmBytes, {});
const exports = wasmModule.instance.exports;

assert.equal(typeof exports.lean_analyzer_version, "function");
assert.equal(exports.lean_analyzer_version(), 100);

// Zero (1) | Positive (2) = NonNegative (3)
const joined = exports.lean_analyzer_join_signs(1, 2);
assert.equal(joined, 3);
console.log("  [PASS] WASM Bitset Lattice Join Execution (1 cycle)");

// NonNegative (3) & Positive (2) = Positive (2)
const met = exports.lean_analyzer_meet_signs(3, 2);
assert.equal(met, 2);
console.log("  [PASS] WASM Bitset Lattice Meet Execution (1 cycle)");

// Test fast ilean parsing via WASM (if an optional sample path is provided via LEAN_ILEAN_SAMPLE)
const ileanSamplePath = process.env.LEAN_ILEAN_SAMPLE || "";
if (ileanSamplePath && fs.existsSync(ileanSamplePath)) {
  const ileanContent = fs.readFileSync(ileanSamplePath);
  const memory = exports.memory;
  const scratchPtr = exports.lean_analyzer_get_scratch_ptr();
  const scratchCapacity = exports.lean_analyzer_get_scratch_len();

  assert.ok(ileanContent.length <= scratchCapacity, "ilean sample exceeds scratch capacity");

  const scratchView = new Uint8Array(memory.buffer, scratchPtr, ileanContent.length);
  scratchView.set(ileanContent);

  // Allocate 4 u32s for out metadata: [version, decls_count, imports_count, refs_count]
  const metaOffset = scratchPtr + Math.ceil((ileanContent.length + 16) / 16) * 16;
  const parseOk = exports.lean_analyzer_parse_ilean_meta(
    scratchPtr,
    ileanContent.length,
    metaOffset,
    metaOffset + 4,
    metaOffset + 8,
    metaOffset + 12
  );
  const metaView = new Uint32Array(memory.buffer, metaOffset, 4);

  assert.equal(parseOk, 1, "Failed to parse ilean in WASM");
  assert.equal(metaView[0], 5, "ILean version should be 5");
  assert.ok(metaView[1] >= 1, "Expected at least 1 declaration");
  console.log(`  [PASS] WASM .ilean Parse: Version ${metaView[0]}, ${metaView[1]} decls, ${metaView[2]} imports, ${metaView[3]} references`);
}

// Test WASM-backed LeanAbstractInterpreter methods (Waves 1-5)
const wasmReduced = interp.reduceState({
  sign: "NON_NEGATIVE",
  interval: { min: 10, max: 22 },
  congruence: { stride: 5, offset: 3 },
  isDeterministic: true,
  purity: "PURE"
});
assert.deepEqual(wasmReduced.interval, { min: 13, max: 18 });
assert.deepEqual(wasmReduced.congruence, { stride: 5, offset: 3 });

const wasmLand = interp.evalExpr({
  op: "Nat.land",
  args: [{ value: 15 }, { value: 6 }]
});
assert.deepEqual(wasmLand.interval, { min: 6, max: 6 });

assert.equal(interp.checkZoneSubDecreasing(-1, 1), "TRUE");
assert.equal(interp.checkZoneSubDecreasing(-1, 0), "FALSE");
console.log("  [PASS] WASM-Accelerated Granger Reduction, Bitwise Interval & Zone Termination");

const wasmOct = interp.reduceOctagonTwoVars(
  { min: 30, max: 100 },
  { min: 0, max: 100 },
  100,
  100
);
assert.ok(wasmOct !== null);
assert.deepEqual(wasmOct[0], { min: 30, max: 100 });
assert.deepEqual(wasmOct[1], { min: 0, max: 70 });

const wasmOctEven = interp.reduceOctagonTwoVars(
  { min: 0, max: 100 },
  { min: 0, max: 100 },
  0,
  5,
  2
);
assert.ok(wasmOctEven !== null);
assert.equal(wasmOctEven[0].max, 3);
console.log("  [PASS] WASM-Accelerated Wave 6 Octagon Relational Domain & Integer Strong Closure");

const wasmWeighted = interp.reduceWeightedLinearTwoVars(
  2,
  3,
  100,
  100,
  { min: 10, max: 100 },
  { min: 0, max: 100 }
);
assert.ok(wasmWeighted !== null);
assert.deepEqual(wasmWeighted[0], { min: 11, max: 50 });
assert.deepEqual(wasmWeighted[1], { min: 0, max: 26 });
console.log("  [PASS] WASM-Accelerated Wave 9 Weighted Linear / Karr Affine Conservation");


const fullBufDiags = diagnoseLeanSourceWasm(
  "def fastDiv (x : Nat) : Nat := x / 64\ntheorem refl_thm (x : Nat) : x = x := by rfl\n",
  1
);
assert.ok(fullBufDiags.some((d) => d.code === "SAIR-LAW-14"), "Expected SAIR-LAW-14 from diagnoseLeanSourceWasm");
assert.ok(fullBufDiags.some((d) => d.code === "FIDELITY-02"), "Expected FIDELITY-02 from diagnoseLeanSourceWasm");
const reflDiag = fullBufDiags.find((d) => d.code === "FIDELITY-02");
assert.ok(reflDiag, "Expected FIDELITY-02 diagnostic");
assert.ok(!reflDiag.hint.includes("eval_nat%"), "Default profile must not recommend custom eval_nat% macro");
assert.ok(!reflDiag.hint.includes("fast_decide"), "Default profile must not recommend custom fast_decide tactic");

const sairDiags = diagnoseLeanSourceWasm(
  "def step (x : Nat) : Nat := by\n  let y := x + 1\n  exact y\ndef nextDef : Nat := 1\n",
  1
);
assert.ok(sairDiags.some((d) => d.code === "SAIR-LAW-03"), "Expected SAIR-LAW-03 for let inside by-block followed by top-level def");
console.log("  [PASS] WASM Full-Buffer UTF-8 Source Diagnostics (lean_analyzer_diagnose_utf8)");

// Test KnownBits64 transfer function in WASM
assert.equal(typeof exports.lean_analyzer_known_bits64_add, "function");
const kbMemory = exports.memory;
const kbScratch = exports.lean_analyzer_get_scratch_ptr();
const kbOutZero = kbScratch + 64;
const kbOutOne = kbScratch + 72;
const kbRc = exports.lean_analyzer_known_bits64_add(
  BigInt.asUintN(64, ~10n),
  10n,
  BigInt.asUintN(64, ~5n),
  5n,
  kbOutZero,
  kbOutOne
);
assert.equal(kbRc, 1);
const kbView = new BigUint64Array(kbMemory.buffer, kbOutZero, 2);
assert.equal(kbView[0], BigInt.asUintN(64, ~15n), "Expected exact KnownBits64 known_zero for 10 + 5 = 15");
assert.equal(kbView[1], 15n, "Expected exact KnownBits64 sum 10 + 5 = 15");
console.log("  [PASS] WASM KnownBits64 Abstract Domain Transfer (lean_analyzer_known_bits64_add)");

console.log("All Real Lean WASM Engine Integration tests passed 100% cleanly!");



