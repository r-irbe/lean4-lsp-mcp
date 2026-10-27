# lean-analyzer User Guide

This guide covers installation, Rust library usage, WebAssembly / JavaScript integration, `.ilean` workspace indexing, Lean 4 formal soundness verification, and oracle regeneration.

---

## 1. Repository Layout

| Path | Purpose |
| :--- | :--- |
| `src/` | Rust library source: abstract domains (`lattice.rs`, `nat_interval.rs`, `congruence.rs`, `zone.rs`, `octagon.rs`), WTO fixpoint engine (`wto.rs`), AST evaluator (`ast.rs`, `ops.rs`, `interpreter.rs`), `.ilean` indexer (`ilean_parser.rs`, `batch_scanner.rs`, `mmap_reader.rs`), and WASM C ABI (`wasm_abi.rs`). |
| `js/lean_analyzer_bridge.js` | Zero-dependency ES module wrapper over `data/lean_analyzer.wasm` with pure-JS fallbacks. |
| `data/lean_analyzer.wasm` | Precompiled `wasm32-unknown-unknown` binary (~49 KB). |
| `lean/` | Self-contained Lean 4 (`v4.34.1`) package proving soundness of the abstract domains (`LeanAnalyzer/AbstractInterpretation.lean`). Zero Mathlib dependency. |
| `tests/` | Unit, property, differential Lean oracle (`test_lean_oracle.rs`), exhaustive small-grid optimality (`test_interval_soundness.rs`), and `.ilean` throughput gates (`test_corpus_gate.rs`, `test_real_ilean_scan.rs`). |
| `examples/corpus_bench.rs` | CLI benchmark tool for `.ilean` directory scanning and symbol lookup latency. |
| `tools/` | `gen_oracle.lean` and `regen_oracle.sh` for regenerating `tests/fixtures/lean_oracle.tsv` from a Lean 4 toolchain. |
| `scripts/build_and_sync_wasm.sh` | Builds `wasm32-unknown-unknown --release` and updates `data/lean_analyzer.wasm`. |

---

## 2. Rust API Usage

Add `lean-analyzer` to your `Cargo.toml`:

```toml
[dependencies]
lean-analyzer = { git = "https://github.com/r-irbe/lean-analyzer" }
```

### 2.1 Evaluating Lean 4 Expressions & Harvesting Diagnostics

```rust
use lean_analyzer::ast::LeanExpr;
use lean_analyzer::interpreter::LeanAbstractInterpreter;
use lean_analyzer::lattice::{AbstractState, IntervalBound};

let mut interp = LeanAbstractInterpreter::new();
interp.bind_var("x", AbstractState::nat_range(2, 5));
interp.bind_var("y", AbstractState::nat_range(10, 20));

// Evaluate `x - y` under Lean 4 total Nat subtraction (`2..5 - 10..20 == 0..0`)
let expr = LeanExpr::app2("Nat.sub", LeanExpr::var("x"), LeanExpr::var("y"));
let state = interp.eval_expr(&expr);
assert_eq!(state.interval, Some(IntervalBound::point(0)));

// Emit actionable static diagnostic certificates (e.g., NatSubTruncation, NatDivModByZero)
let certs = interp.diagnose_expr(&expr);
assert!(!certs.is_empty());
println!("{}: {}", certs[0].summary, certs[0].hint);
```

### 2.2 Mutual Granger Interval-Congruence Reduction

```rust
use lean_analyzer::congruence::{reduce_interval_congruence, NatCongruence};
use lean_analyzer::lattice::IntervalBound;

let iv = IntervalBound::new(1, 299);
let cong = NatCongruence::new(100, 0); // 0 (mod 100)
let (tight_iv, tight_cong) = reduce_interval_congruence(iv, cong);
assert_eq!(tight_iv, IntervalBound::new(100, 200));
```

### 2.3 Relational Zone (DBM) & Octagon Domains

```rust
use lean_analyzer::zone::NatZoneDomain;
use lean_analyzer::octagon::NatOctagonDomain;
use lean_analyzer::lattice::IntervalBound;

// Zone DBM: prove `n - (i + 1) < n - i` when `i < n` (`i - n <= -1`)
let mut zone = NatZoneDomain::top(2); // var 1 = i, var 2 = n
zone.add_constraint(1, 2, -1);        // i - n <= -1
assert!(zone.close());
assert!(zone.verify_strict_decrease(2, 1, 1));

// Two-variable Octagon reduction: v0 in [30, 100], v1 in [0, 100], v0 + v1 == 100
let iv0 = IntervalBound::new(30, 100);
let iv1 = IntervalBound::new(0, 100);
let (r0, r1) = NatOctagonDomain::reduce_two_vars(iv0, iv1, Some(100), Some(100), None).unwrap();
assert_eq!(r0, IntervalBound::new(30, 100));
assert_eq!(r1, IntervalBound::new(0, 70));
```

### 2.4 Zero-Copy `.ilean` Indexing & Incremental Daemon Updates

```rust
use lean_analyzer::batch_scanner::{BatchILeanScanner, DaemonIndexTracker};
use std::path::Path;

let mut scanner = BatchILeanScanner::new();
let files_scanned = scanner.scan_directory(Path::new(".lake/build/lib"))?;
println!("Scanned {} .ilean files ({} symbols)", files_scanned, scanner.total_symbols());

if let Some(decl) = scanner.lookup("MyModule.my_theorem") {
    println!("Found in {} at {:?}", decl.module, decl.range);
}

// Incremental mtime-based polling for language servers / editor plugins:
let mut daemon = DaemonIndexTracker::new();
let delta = daemon.poll_and_update(Path::new(".lake/build/lib"))?;
println!("Added: {}, Modified: {}, Removed: {}", delta.files_added, delta.files_modified, delta.files_removed);
```

---

## 3. WebAssembly & JavaScript Bridge (`js/lean_analyzer_bridge.js`)

The ES module `js/lean_analyzer_bridge.js` loads `data/lean_analyzer.wasm` automatically in Node.js (or accepts a `Uint8Array` / `ArrayBuffer` / URL in browsers) and provides:

| Method | Description |
| :--- | :--- |
| `getVersion()` | Returns the ABI version integer (`100`). |
| `joinSigns(a, b)` / `meetSigns(a, b)` | 3-bit sign lattice join (`\|`) and meet (`&`). |
| `evalNatAdd(min1, max1, min2, max2)` | Interval bound for `a + b`. |
| `evalNatSub(min1, max1, min2, max2)` | Saturating interval bound for `a - b` (`Nat.sub`). |
| `evalNatMul(min1, max1, min2, max2)` | Interval bound for `a * b`. |
| `evalNatDiv(min1, max1, min2, max2)` | Total interval bound for `a / b` (`a / 0 = 0`). |
| `evalNatMod(min1, max1, min2, max2)` | Exact single-bucket and general interval bound for `a % b` (`a % 0 = a`). |
| `evalNatLand` / `evalNatLor` / `evalNatXor` | Exact Warren (Ch. 4) bitwise interval bounds over `[min1, max1]` and `[min2, max2]`. |
| `evalNatShl` / `evalNatShr` | Bitwise shift interval bounds `a <<< b` and `a >>> b`. |
| `reduceIntervalCongruence(min, max, stride, offset)` | Mutual Granger reduction returning `{ min, max, stride, offset }` or `null` (`Bottom`). |
| `checkZoneSubDecreasing(guardDiff, step)` | Checks `n - (i + step) < n - i` under `i - n <= guardDiff`. |
| `reduceOctagonTwoVars(min0, max0, min1, max1, sumLo, sumHi, diffHi)` | Tightens two `Nat` intervals under `sumLo <= x0 + x1 <= sumHi` and `x0 - x1 <= diffHi`. |
| `diagnoseNatOp(op, min1, max1, min2, max2)` | Emits `NatSubTruncation` and `NatDivModByZero` diagnostic certificates. |

---

## 4. Formal Soundness Proofs (`lean/`) & Differential Oracle (`tools/`)

### 4.1 Building the Lean 4 Soundness Proofs

The `lean/` directory is a standalone Lean 4 package (`LeanAnalyzer.AbstractInterpretation`) with zero external dependencies (no Mathlib download required):

```bash
cd lean
lake build
```

It mechanically proves:
- `AbstractSign`: `from_to_bitmask`, `bitmask_join_compat`, `bitmask_meet_compat`, `join_sound_zero_pos`, `meet_sound_nonNeg_pos`.
- `NatInterval`: `join_sound`, `meet_sound`, `add_sound`, `sub_sound`, `land_upper_bound_sound`, `lor_lower_bound_sound`, `mod_upper_bound_sound`, `widenThreshold_sound_prev`, `widenThreshold_sound_next`, `natSubTruncation_cert_sound`, `divByZeroGuard_cert_sound`.
- `NatCongruence` & `ReducedNatProduct`: `addSameStride_sound`, `scale_sound`, `reduce_point_sound`, `singleton_exact`.
- `ZoneBound`: `id_sound`, `compose_sound`, `closure_step_sound`, `strict_decrease_sound`, `check_sub_decreasing_sound`.
- `OctagonBound` & `NatOctagon2`: `sum_diff_double_bound`, `simplex_complement_sound`, `strengthen_upper0_sound`, `strengthen_lower0_sound`, `close_sound`.

### 4.2 Regenerating the Differential Oracle

When bumping `lean/lean-toolchain` to a newer Lean 4 release, regenerate `tests/fixtures/lean_oracle.tsv` and re-run the differential test suite:

```bash
bash tools/regen_oracle.sh
cargo test --test test_lean_oracle
```

### 4.3 Benchmarking `.ilean` Scan Throughput

To benchmark `.ilean` indexing and symbol lookup latency on any compiled Lean 4 project `.lake/build/lib` directory:

```bash
cargo run --release --example corpus_bench -- /path/to/.lake/build/lib 5
```
