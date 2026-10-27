/**
 * js/lean_analyzer_bridge.js
 * In-process WebAssembly & ES module abstract evaluation bridge for Lean 4 terms.
 */

export const AbstractSign = Object.freeze({
  Bottom: 0,
  Zero: 1,
  Positive: 2,
  NonNegative: 3,
  Negative: 4,
  NonPositive: 5,
  NonZero: 6,
  Top: 7
});

export const AbstractBool = Object.freeze({
  Bottom: 0,
  False: 1,
  True: 2,
  Top: 3
});

export const DiagnosticKind = Object.freeze({
  NatSubTruncation: "NatSubTruncation",
  NatDivModByZero: "NatDivModByZero",
  DeadBranch: "DeadBranch"
});

export class LeanAnalyzerBridge {
  constructor(wasmInstance = null) {
    this.wasm = wasmInstance;
    this.memory = wasmInstance ? wasmInstance.exports.memory : null;
  }

  getVersion() {
    if (this.wasm && this.wasm.exports.lean_analyzer_version) {
      return this.wasm.exports.lean_analyzer_version();
    }
    return 100;
  }

  joinSigns(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_join_signs) {
      return this.wasm.exports.lean_analyzer_join_signs(a, b);
    }
    return (a | b) & 7;
  }

  meetSigns(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_meet_signs) {
      return this.wasm.exports.lean_analyzer_meet_signs(a, b);
    }
    return (a & b) & 7;
  }

  _callWasmIntervalOp(fnName, min1, max1, min2, max2) {
    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports[fnName] === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = this.wasm.exports[fnName](
        BigInt(Math.trunc(min1)),
        BigInt(Math.trunc(max1)),
        BigInt(Math.trunc(min2)),
        BigInt(Math.trunc(max2)),
        ptr
      );
      if (ok === 1) {
        const view = new BigInt64Array(this.memory.buffer, ptr, 2);
        return { min: Number(view[0]), max: Number(view[1]) };
      }
    }
    return null;
  }

  evalNatAdd(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_add", min1, max1, min2, max2);
    if (w) return w;
    return {
      min: Math.max(0, min1 + min2),
      max: Math.max(0, max1 + max2)
    };
  }

  evalNatSub(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_sub", min1, max1, min2, max2);
    if (w) return w;
    return {
      min: Math.max(0, min1 - max2),
      max: Math.max(0, max1 - min2)
    };
  }

  evalNatMul(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_mul", min1, max1, min2, max2);
    if (w) return w;
    const p1 = min1 * min2;
    const p2 = min1 * max2;
    const p3 = max1 * min2;
    const p4 = max1 * max2;
    return {
      min: Math.max(0, Math.min(p1, p2, p3, p4)),
      max: Math.max(0, Math.max(p1, p2, p3, p4))
    };
  }

  evalBoolNot(val) {
    if (this.wasm && this.wasm.exports.lean_analyzer_bool_not) {
      return this.wasm.exports.lean_analyzer_bool_not(val);
    }
    switch (val) {
      case AbstractBool.False: return AbstractBool.True;
      case AbstractBool.True: return AbstractBool.False;
      case AbstractBool.Bottom: return AbstractBool.Bottom;
      default: return AbstractBool.Top;
    }
  }

  evalBoolAnd(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_bool_and) {
      return this.wasm.exports.lean_analyzer_bool_and(a, b);
    }
    if (a === AbstractBool.False || b === AbstractBool.False) {
      return AbstractBool.False;
    }
    if (a === AbstractBool.True && b === AbstractBool.True) {
      return AbstractBool.True;
    }
    if (a === AbstractBool.Bottom || b === AbstractBool.Bottom) {
      return AbstractBool.Bottom;
    }
    return AbstractBool.Top;
  }

  evalBoolOr(a, b) {
    if (this.wasm && this.wasm.exports.lean_analyzer_bool_or) {
      return this.wasm.exports.lean_analyzer_bool_or(a, b);
    }
    if (a === AbstractBool.True || b === AbstractBool.True) {
      return AbstractBool.True;
    }
    if (a === AbstractBool.False && b === AbstractBool.False) {
      return AbstractBool.False;
    }
    if (a === AbstractBool.Bottom || b === AbstractBool.Bottom) {
      return AbstractBool.Bottom;
    }
    return AbstractBool.Top;
  }

  evalBoolXor(a, b) {
    if (a === AbstractBool.Bottom || b === AbstractBool.Bottom) {
      return AbstractBool.Bottom;
    }
    if ((a === AbstractBool.True && b === AbstractBool.True) || (a === AbstractBool.False && b === AbstractBool.False)) {
      return AbstractBool.False;
    }
    if ((a === AbstractBool.True && b === AbstractBool.False) || (a === AbstractBool.False && b === AbstractBool.True)) {
      return AbstractBool.True;
    }
    return AbstractBool.Top;
  }

  evalNatPow(min1, max1, min2, max2) {
    if (max2 === 0) {
      return { min: 1, max: 1 };
    }
    return {
      min: Math.max(0, Math.pow(Math.max(0, min1), Math.max(0, min2))),
      max: Math.max(0, Math.pow(Math.max(0, max1), Math.max(0, max2)))
    };
  }

  evalNatMin(min1, max1, min2, max2) {
    return {
      min: Math.min(min1, min2),
      max: Math.min(max1, max2)
    };
  }

  evalNatMax(min1, max1, min2, max2) {
    return {
      min: Math.max(min1, min2),
      max: Math.max(max1, max2)
    };
  }

  /**
   * Lean 4 Nat division interval transfer (`a / 0 = 0`).
   */
  evalNatDiv(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_div", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (bHi === 0) {
      return { min: 0, max: 0 };
    }
    if (bLo > 0) {
      return {
        min: Math.trunc(aLo / bHi),
        max: Math.trunc(aHi / bLo)
      };
    }
    // bLo === 0 && bHi > 0: divisor may be 0 (giving 0) or in [1, bHi].
    return {
      min: 0,
      max: aHi
    };
  }

  /**
   * Lean 4 Nat modulo interval transfer (`a % 0 = a`), including single-quotient-bucket exactness.
   */
  evalNatMod(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_mod", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (bHi === 0) {
      return { min: aLo, max: aHi };
    }
    if (bLo === bHi && bLo > 0) {
      const k = bLo;
      if (Math.trunc(aLo / k) === Math.trunc(aHi / k)) {
        return { min: aLo % k, max: aHi % k };
      }
      return { min: 0, max: Math.min(aHi, k - 1) };
    }
    if (bLo > 0) {
      if (aHi < bLo) {
        return { min: aLo, max: aHi };
      }
      return { min: 0, max: Math.min(aHi, bHi - 1) };
    }
    // Divisor includes 0 (`a % 0 = a`) and positive values up to `bHi`:
    return { min: 0, max: aHi };
  }

  /**
   * Bitwise AND interval transfer (Warren Ch. 4 bounds).
   */
  evalNatLand(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_land", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (aLo === aHi && bLo === bHi) {
      const v = Number(BigInt(aLo) & BigInt(bLo));
      return { min: v, max: v };
    }
    return { min: 0, max: Math.min(aHi, bHi) };
  }

  /**
   * Bitwise OR interval transfer (Warren Ch. 4 bounds via next power of two minus 1).
   */
  evalNatLor(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_lor", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (aLo === aHi && bLo === bHi) {
      const v = Number(BigInt(aLo) | BigInt(bLo));
      return { min: v, max: v };
    }
    const lo = Math.max(aLo, bLo);
    const maxIn = Math.max(aHi, bHi);
    if (maxIn === 0) {
      return { min: 0, max: 0 };
    }
    let mask = 1n;
    const bigMax = BigInt(maxIn);
    while (mask <= bigMax) {
      mask <<= 1n;
    }
    return { min: lo, max: Number(mask - 1n) };
  }

  /**
   * Bitwise XOR interval transfer (Warren Ch. 4 bounds).
   */
  evalNatXor(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_xor", min1, max1, min2, max2);
    if (w) return w;
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    if (aLo === aHi && bLo === bHi) {
      const v = Number(BigInt(aLo) ^ BigInt(bLo));
      return { min: v, max: v };
    }
    const maxIn = Math.max(aHi, bHi);
    if (maxIn === 0) {
      return { min: 0, max: 0 };
    }
    let mask = 1n;
    const bigMax = BigInt(maxIn);
    while (mask <= bigMax) {
      mask <<= 1n;
    }
    return { min: 0, max: Number(mask - 1n) };
  }

  /**
   * Bitwise shift-left interval transfer `a <<< b`.
   */
  evalNatShl(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_shl", min1, max1, min2, max2);
    if (w) return w;
    const aLo = BigInt(Math.max(0, Math.trunc(min1)));
    const aHi = BigInt(Math.max(Number(aLo), Math.trunc(max1)));
    const bLo = BigInt(Math.max(0, Math.trunc(min2)));
    const bHi = BigInt(Math.max(Number(bLo), Math.trunc(max2)));
    return {
      min: Number(aLo << bLo),
      max: Number(aHi << bHi)
    };
  }

  /**
   * Bitwise shift-right interval transfer `a >>> b`.
   */
  evalNatShr(min1, max1, min2, max2) {
    const w = this._callWasmIntervalOp("lean_analyzer_eval_nat_shr", min1, max1, min2, max2);
    if (w) return w;
    const aLo = BigInt(Math.max(0, Math.trunc(min1)));
    const aHi = BigInt(Math.max(Number(aLo), Math.trunc(max1)));
    const bLo = BigInt(Math.max(0, Math.trunc(min2)));
    const bHi = BigInt(Math.max(Number(bLo), Math.trunc(max2)));
    return {
      min: Number(aLo >> bHi),
      max: Number(aHi >> bLo)
    };
  }

  /**
   * Mutual Granger reduction of interval `[min, max]` against congruence `offset (mod stride)`.
   * Returns `{ min, max, stride, offset }` or `null` if the intersection is empty (Bottom).
   */
  reduceIntervalCongruence(min, max, stride, offset) {
    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_reduce_interval_congruence === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = this.wasm.exports.lean_analyzer_reduce_interval_congruence(
        BigInt(Math.trunc(min)),
        BigInt(Math.trunc(max)),
        BigInt(Math.max(0, Math.trunc(stride))),
        BigInt(Math.max(0, Math.trunc(offset))),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.memory.buffer, ptr, 4);
      return {
        min: Number(view[0]),
        max: Number(view[1]),
        stride: Number(view[2]),
        offset: Number(view[3])
      };
    }
    const lo = Math.max(0, Math.trunc(min));
    const hi = Math.trunc(max);
    if (lo > hi) {
      return null;
    }
    const s = Math.max(0, Math.trunc(stride));
    const o = s === 0 ? Math.max(0, Math.trunc(offset)) : ((Math.trunc(offset) % s) + s) % s;
    if (s === 0) {
      if (o >= lo && o <= hi) {
        return { min: o, max: o, stride: 0, offset: o };
      }
      return null;
    }
    const remLo = lo % s;
    const deltaLo = remLo <= o ? (o - remLo) : (s - (remLo - o));
    const tightMin = lo + deltaLo;
    if (tightMin > hi) {
      return null;
    }
    const remHi = hi % s;
    const deltaHi = remHi >= o ? (remHi - o) : (s - (o - remHi));
    const tightMax = hi - deltaHi;
    if (tightMin > tightMax) {
      return null;
    }
    if (tightMin === tightMax) {
      return { min: tightMin, max: tightMax, stride: 0, offset: tightMin };
    }
    return { min: tightMin, max: tightMax, stride: s, offset: o };
  }

  /**
   * Discharges Lean 4 termination obligation `n - (i + step) < n - i` under guard `i - n <= guardDiff`.
   * Returns `AbstractBool` (`Bottom=0, False=1, True=2, Top=3`).
   */
  checkZoneSubDecreasing(guardDiff, step) {
    if (this.wasm && this.wasm.exports.lean_analyzer_zone_check_sub_decreasing) {
      return this.wasm.exports.lean_analyzer_zone_check_sub_decreasing(
        BigInt(Math.trunc(guardDiff)),
        BigInt(Math.trunc(step))
      );
    }
    if (step <= 0) {
      return AbstractBool.False;
    }
    if (guardDiff <= -1) {
      return AbstractBool.True;
    }
    return AbstractBool.Top;
  }

  /**
   * Emits actionable static diagnostic certificates for a binary Nat operation on `[min1, max1]` and `[min2, max2]`.
   */
  diagnoseNatOp(op, min1, max1, min2, max2) {
    const aLo = Math.max(0, Math.trunc(min1));
    const aHi = Math.max(aLo, Math.trunc(max1));
    const bLo = Math.max(0, Math.trunc(min2));
    const bHi = Math.max(bLo, Math.trunc(max2));
    const certs = [];
    if (op === "Nat.sub" || op === "HSub.hSub" || op === "-") {
      if (aHi <= bLo && bLo > 0) {
        certs.push({
          kind: DiagnosticKind.NatSubTruncation,
          operator: op,
          summary: `Natural subtraction \`${op}\` on [${aLo}, ${aHi}] - [${bLo}, ${bHi}] saturates to [0, 0].`,
          hint: "Add guard `b <= a` or switch to `Int` subtraction if negative values are intended."
        });
      }
    } else if (
      op === "Nat.div" ||
      op === "HDiv.hDiv" ||
      op === "/" ||
      op === "Nat.mod" ||
      op === "HMod.hMod" ||
      op === "%"
    ) {
      if (bLo <= 0 && 0 <= bHi) {
        certs.push({
          kind: DiagnosticKind.NatDivModByZero,
          operator: op,
          summary: `Divisor interval [${bLo}, ${bHi}] in \`${op}\` includes 0 (Lean total semantics: a / 0 = 0, a % 0 = a).`,
          hint: "Prove `0 < divisor` or guard against zero divisor."
        });
      }
    }
    return certs;
  }

  /**
   * Tightens two natural-number intervals `[min0, max0]` and `[min1, max1]`
   * under relational octagon constraints `sumLo <= x0 + x1 <= sumHi` and `x0 - x1 <= diffHi`.
   * Returns `[{ min, max }, { min, max }]` or `null` if unsatisfiable (`Bottom`).
   */
  reduceOctagonTwoVars(min0, max0, min1, max1, sumLo, sumHi, diffHi = Number.POSITIVE_INFINITY) {
    const MAX_I64 = 9223372036854775807n;
    const toI64 = (v) => (!Number.isFinite(v) ? MAX_I64 : BigInt(Math.trunc(v)));

    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_octagon_reduce_two_vars === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = this.wasm.exports.lean_analyzer_octagon_reduce_two_vars(
        toI64(Math.max(0, min0)),
        toI64(max0),
        toI64(Math.max(0, min1)),
        toI64(max1),
        toI64(Math.max(0, sumLo)),
        toI64(sumHi),
        toI64(diffHi),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.memory.buffer, ptr, 4);
      const fromI64 = (b) => (b >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(b));
      return [
        { min: fromI64(view[0]), max: fromI64(view[1]) },
        { min: fromI64(view[2]), max: fromI64(view[3]) }
      ];
    }

    let lo0 = Math.max(0, Math.trunc(min0));
    let hi0 = Number.isFinite(max0) ? Math.trunc(max0) : Number.POSITIVE_INFINITY;
    let lo1 = Math.max(0, Math.trunc(min1));
    let hi1 = Number.isFinite(max1) ? Math.trunc(max1) : Number.POSITIVE_INFINITY;
    const sLo = Math.max(0, Math.trunc(sumLo));
    const sHi = Number.isFinite(sumHi) ? Math.trunc(sumHi) : Number.POSITIVE_INFINITY;
    const dHi = Number.isFinite(diffHi) ? Math.trunc(diffHi) : Number.POSITIVE_INFINITY;

    for (let iter = 0; iter < 4; iter++) {
      if (Number.isFinite(hi1)) lo0 = Math.max(lo0, sLo - hi1);
      if (Number.isFinite(sHi)) hi0 = Math.min(hi0, sHi - lo1);
      if (Number.isFinite(hi0)) lo1 = Math.max(lo1, sLo - hi0);
      if (Number.isFinite(sHi)) hi1 = Math.min(hi1, sHi - lo0);

      if (Number.isFinite(dHi)) {
        if (Number.isFinite(hi1)) hi0 = Math.min(hi0, hi1 + dHi);
        lo1 = Math.max(lo1, lo0 - dHi);
        if (Number.isFinite(sHi)) {
          hi0 = Math.min(hi0, Math.floor((sHi + dHi) / 2));
        }
      }
      if (lo0 > hi0 || lo1 > hi1) return null;
    }

    if (lo0 + lo1 > sHi || hi0 + hi1 < sLo) return null;
    if (Number.isFinite(dHi) && lo0 - hi1 > dHi) return null;

    return [
      { min: lo0, max: hi0 },
      { min: lo1, max: hi1 }
    ];
  }

  /**
   * Tightens two natural-number intervals `[xMin, xMax]` and `[yMin, yMax]`
   * under a weighted linear / Karr affine conservation bound `sumMin <= a * x + b * y <= sumMax`
   * (`a > 0`, `b > 0`).
   * Returns `[{ min, max }, { min, max }]` or `null` if unsatisfiable (`Bottom`).
   */
  reduceWeightedLinearTwoVars(a, b, sumMin, sumMax, xMin, xMax, yMin, yMax) {
    const MAX_I64 = 9223372036854775807n;
    const toI64 = (v) => (!Number.isFinite(v) ? MAX_I64 : BigInt(Math.trunc(v)));

    const wasmFn =
      this.wasm && this.wasm.exports
        ? this.wasm.exports.lean_analyzer_weighted_linear_reduce ||
          this.wasm.exports.lean_analyzer_WeightedSimplexReduce
        : null;
    if (
      typeof wasmFn === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const ok = wasmFn.call(
        this.wasm.exports,
        toI64(a),
        toI64(b),
        toI64(Math.max(0, sumMin)),
        toI64(sumMax),
        toI64(Math.max(0, xMin)),
        toI64(xMax),
        toI64(Math.max(0, yMin)),
        toI64(yMax),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.memory.buffer, ptr, 4);
      const fromI64 = (v) => (v >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(v));
      return [
        { min: fromI64(view[0]), max: fromI64(view[1]) },
        { min: fromI64(view[2]), max: fromI64(view[3]) }
      ];
    }

    const wa = Math.trunc(a);
    const wb = Math.trunc(b);
    if (wa <= 0 || wb <= 0) return null;
    let xLo = Math.max(0, Math.trunc(xMin));
    let xHi = Number.isFinite(xMax) ? Math.trunc(xMax) : Number.POSITIVE_INFINITY;
    let yLo = Math.max(0, Math.trunc(yMin));
    let yHi = Number.isFinite(yMax) ? Math.trunc(yMax) : Number.POSITIVE_INFINITY;
    if (xLo > xHi || yLo > yHi) return null;

    const sLo = Math.max(0, Math.trunc(sumMin));
    const sHi = Number.isFinite(sumMax) ? Math.trunc(sumMax) : Number.POSITIVE_INFINITY;
    if (sLo > sHi) return null;

    for (let iter = 0; iter < 3; iter++) {
      if (Number.isFinite(sHi)) {
        const remU = sHi - wb * yLo;
        if (remU < 0) return null;
        xHi = Math.min(xHi, Math.floor(remU / wa));
      }
      if (Number.isFinite(yHi) && sLo > 0) {
        const remL = Math.max(0, sLo - wb * yHi);
        xLo = Math.max(xLo, Math.ceil(remL / wa));
      }
      if (xLo > xHi) return null;

      if (Number.isFinite(sHi)) {
        const remU = sHi - wa * xLo;
        if (remU < 0) return null;
        yHi = Math.min(yHi, Math.floor(remU / wb));
      }
      if (Number.isFinite(xHi) && sLo > 0) {
        const remL = Math.max(0, sLo - wa * xHi);
        yLo = Math.max(yLo, Math.ceil(remL / wb));
      }
      if (yLo > yHi) return null;
    }

    if (Number.isFinite(sHi) && wa * xLo + wb * yLo > sHi) return null;
    if (Number.isFinite(xHi) && Number.isFinite(yHi) && wa * xHi + wb * yHi < sLo) return null;

    return [
      { min: xLo, max: xHi },
      { min: yLo, max: yHi }
    ];
  }

  /**
   * Relational `<=` comparison across intervals (`Bottom=0, False=1, True=2, Top=3`).
   */
  evalNatBle(min1, max1, min2, max2) {
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_eval_nat_ble === "function") {
      return this.wasm.exports.lean_analyzer_eval_nat_ble(
        BigInt(Math.trunc(min1)),
        BigInt(Math.trunc(max1)),
        BigInt(Math.trunc(min2)),
        BigInt(Math.trunc(max2))
      );
    }
    if (min1 > max1 || min2 > max2) return AbstractBool.Bottom;
    if (max1 <= min2) return AbstractBool.True;
    if (min1 > max2) return AbstractBool.False;
    return AbstractBool.Top;
  }

  /**
   * Relational `<` comparison across intervals (`Bottom=0, False=1, True=2, Top=3`).
   */
  evalNatBlt(min1, max1, min2, max2) {
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_eval_nat_blt === "function") {
      return this.wasm.exports.lean_analyzer_eval_nat_blt(
        BigInt(Math.trunc(min1)),
        BigInt(Math.trunc(max1)),
        BigInt(Math.trunc(min2)),
        BigInt(Math.trunc(max2))
      );
    }
    if (min1 > max1 || min2 > max2) return AbstractBool.Bottom;
    if (max1 < min2) return AbstractBool.True;
    if (min1 >= max2) return AbstractBool.False;
    return AbstractBool.Top;
  }

  /**
   * Relational `==` comparison across intervals (`Bottom=0, False=1, True=2, Top=3`).
   */
  evalNatBeq(min1, max1, min2, max2) {
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_eval_nat_beq === "function") {
      return this.wasm.exports.lean_analyzer_eval_nat_beq(
        BigInt(Math.trunc(min1)),
        BigInt(Math.trunc(max1)),
        BigInt(Math.trunc(min2)),
        BigInt(Math.trunc(max2))
      );
    }
    if (min1 > max1 || min2 > max2) return AbstractBool.Bottom;
    if (min1 === max1 && min2 === max2 && min1 === min2) return AbstractBool.True;
    if (max1 < min2 || max2 < min1) return AbstractBool.False;
    return AbstractBool.Top;
  }

  joinBools(a, b) {
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_join_bools === "function") {
      return this.wasm.exports.lean_analyzer_join_bools(a, b);
    }
    return (a | b) & 3;
  }

  meetBools(a, b) {
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_meet_bools === "function") {
      return this.wasm.exports.lean_analyzer_meet_bools(a, b);
    }
    return (a & b) & 3;
  }

  packedJoin(v1, v2) {
    const b1 = BigInt(v1);
    const b2 = BigInt(v2);
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_packed_join === "function") {
      return this.wasm.exports.lean_analyzer_packed_join(b1, b2);
    }
    return b1 | b2;
  }

  packedMeet(v1, v2) {
    const b1 = BigInt(v1);
    const b2 = BigInt(v2);
    if (this.wasm && typeof this.wasm.exports.lean_analyzer_packed_meet === "function") {
      return this.wasm.exports.lean_analyzer_packed_meet(b1, b2);
    }
    return b1 & b2;
  }

  widenInterval(min1, max1, min2, max2) {
    const MAX_I64 = 9223372036854775807n;
    const MIN_I64 = -9223372036854775808n;
    const toI64 = (v) => {
      if (v === Number.POSITIVE_INFINITY) return MAX_I64;
      if (v === Number.NEGATIVE_INFINITY) return MIN_I64;
      return BigInt(Math.trunc(v));
    };
    const fromI64 = (b) => {
      if (b >= MAX_I64) return Number.POSITIVE_INFINITY;
      if (b <= MIN_I64) return Number.NEGATIVE_INFINITY;
      return Number(b);
    };
    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_widen_interval === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const resMin = this.wasm.exports.lean_analyzer_widen_interval(
        toI64(min1),
        toI64(max1),
        toI64(min2),
        toI64(max2),
        ptr
      );
      const view = new BigInt64Array(this.memory.buffer, ptr, 1);
      return { min: fromI64(resMin), max: fromI64(view[0]) };
    }
    return {
      min: min2 < min1 ? Number.NEGATIVE_INFINITY : min1,
      max: max2 > max1 ? Number.POSITIVE_INFINITY : max1
    };
  }

  narrowInterval(min1, max1, min2, max2) {
    const MAX_I64 = 9223372036854775807n;
    const MIN_I64 = -9223372036854775808n;
    const toI64 = (v) => {
      if (v === Number.POSITIVE_INFINITY) return MAX_I64;
      if (v === Number.NEGATIVE_INFINITY) return MIN_I64;
      return BigInt(Math.trunc(v));
    };
    const fromI64 = (b) => {
      if (b >= MAX_I64) return Number.POSITIVE_INFINITY;
      if (b <= MIN_I64) return Number.NEGATIVE_INFINITY;
      return Number(b);
    };
    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_narrow_interval === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const resMin = this.wasm.exports.lean_analyzer_narrow_interval(
        toI64(min1),
        toI64(max1),
        toI64(min2),
        toI64(max2),
        ptr
      );
      const view = new BigInt64Array(this.memory.buffer, ptr, 1);
      return { min: fromI64(resMin), max: fromI64(view[0]) };
    }
    return {
      min: min1 === Number.NEGATIVE_INFINITY ? min2 : min1,
      max: max1 === Number.POSITIVE_INFINITY ? max2 : max1
    };
  }

  /**
   * Threshold widening over integer intervals `[min1, max1]` and `[min2, max2]` with sorted `thresholds`.
   */
  widenWithThresholds(min1, max1, min2, max2, thresholds = []) {
    const MAX_I64 = 9223372036854775807n;
    const MIN_I64 = -9223372036854775808n;
    const toI64 = (v) => {
      if (v === Number.POSITIVE_INFINITY) return MAX_I64;
      if (v === Number.NEGATIVE_INFINITY) return MIN_I64;
      return BigInt(Math.trunc(v));
    };
    const fromI64 = (b) => {
      if (b >= MAX_I64) return Number.POSITIVE_INFINITY;
      if (b <= MIN_I64) return Number.NEGATIVE_INFINITY;
      return Number(b);
    };
    const sorted = [...thresholds].filter(Number.isFinite).map((t) => Math.trunc(t)).sort((a, b) => a - b);

    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_widen_with_thresholds === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const outPtr = ptr;
      const threshPtr = ptr + 16;
      const threshView = new BigInt64Array(this.memory.buffer, threshPtr, sorted.length);
      for (let i = 0; i < sorted.length; i++) {
        threshView[i] = BigInt(sorted[i]);
      }
      const ok = this.wasm.exports.lean_analyzer_widen_with_thresholds(
        toI64(min1),
        toI64(max1),
        toI64(min2),
        toI64(max2),
        threshPtr,
        sorted.length,
        outPtr
      );
      if (ok === 1) {
        const outView = new BigInt64Array(this.memory.buffer, outPtr, 2);
        return { min: fromI64(outView[0]), max: fromI64(outView[1]) };
      }
    }

    let min = min1;
    if (min2 < min1) {
      let found = null;
      for (let i = sorted.length - 1; i >= 0; i--) {
        if (sorted[i] <= min2) {
          found = sorted[i];
          break;
        }
      }
      min = found !== null ? found : (min1 >= 0 && min2 >= 0 ? 0 : Number.NEGATIVE_INFINITY);
    }

    let max = max1;
    if (max2 > max1) {
      let found = null;
      for (let i = 0; i < sorted.length; i++) {
        if (sorted[i] >= max2) {
          found = sorted[i];
          break;
        }
      }
      max = found !== null ? found : Number.POSITIVE_INFINITY;
    }

    return { min, max };
  }

  /**
   * Parses `.ilean` metadata from a `Uint8Array` or UTF-8 string using WASM or JS fallback.
   * Returns `{ version, declsCount, importsCount, refsCount }` or `null` on invalid input.
   */
  parseIleanMeta(input) {
    const bytes = typeof input === "string" ? new TextEncoder().encode(input) : input;
    if (!(bytes instanceof Uint8Array) || bytes.length === 0) {
      return null;
    }

    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_parse_ilean_meta === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function" &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_len === "function"
    ) {
      const scratchPtr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const scratchLen = this.wasm.exports.lean_analyzer_get_scratch_len();
      const headerBytes = 16; // 4 x u32 output slots
      if (bytes.length + headerBytes <= scratchLen) {
        const dataPtr = scratchPtr + headerBytes;
        new Uint8Array(this.memory.buffer, dataPtr, bytes.length).set(bytes);
        const ok = this.wasm.exports.lean_analyzer_parse_ilean_meta(
          dataPtr,
          bytes.length,
          scratchPtr,
          scratchPtr + 4,
          scratchPtr + 8,
          scratchPtr + 12
        );
        if (ok === 1) {
          const out = new Uint32Array(this.memory.buffer, scratchPtr, 4);
          return {
            version: out[0],
            declsCount: out[1],
            importsCount: out[2],
            refsCount: out[3]
          };
        }
        return null;
      }
    }

    try {
      const text = typeof input === "string" ? input : new TextDecoder().decode(bytes);
      const parsed = JSON.parse(text);
      if (!parsed || typeof parsed !== "object") return null;
      return {
        version: typeof parsed.version === "number" ? parsed.version : 1,
        declsCount: parsed.decls && typeof parsed.decls === "object" ? Object.keys(parsed.decls).length : 0,
        importsCount: Array.isArray(parsed.directImports) ? parsed.directImports.length : 0,
        refsCount: parsed.references && typeof parsed.references === "object" ? Object.keys(parsed.references).length : 0
      };
    } catch {
      return null;
    }
  }

  /**
   * Finds the declaration covering 1-indexed `(line, col)` in an `.ilean` JSON buffer.
   * Returns the declaration name string or `null` if none matches.
   */
  findDeclAt(input, line, col) {
    const bytes = typeof input === "string" ? new TextEncoder().encode(input) : input;
    if (!(bytes instanceof Uint8Array) || bytes.length === 0) {
      return null;
    }

    if (
      this.wasm &&
      this.wasm.exports &&
      typeof this.wasm.exports.lean_analyzer_find_decl_at === "function" &&
      this.memory &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_ptr === "function" &&
      typeof this.wasm.exports.lean_analyzer_get_scratch_len === "function"
    ) {
      const scratchPtr = this.wasm.exports.lean_analyzer_get_scratch_ptr();
      const scratchLen = this.wasm.exports.lean_analyzer_get_scratch_len();
      const maxNameLen = 1024;
      if (bytes.length + maxNameLen <= scratchLen) {
        const namePtr = scratchPtr;
        const dataPtr = scratchPtr + maxNameLen;
        new Uint8Array(this.memory.buffer, dataPtr, bytes.length).set(bytes);
        const written = this.wasm.exports.lean_analyzer_find_decl_at(
          dataPtr,
          bytes.length,
          line >>> 0,
          col >>> 0,
          namePtr,
          maxNameLen
        );
        if (written > 0) {
          return new TextDecoder().decode(new Uint8Array(this.memory.buffer, namePtr, written));
        }
        return null;
      }
    }

    try {
      const text = typeof input === "string" ? input : new TextDecoder().decode(bytes);
      const parsed = JSON.parse(text);
      if (!parsed || !parsed.decls || typeof parsed.decls !== "object") return null;
      for (const [name, coords] of Object.entries(parsed.decls)) {
        if (Array.isArray(coords) && coords.length >= 4) {
          const [sLine, sCol, eLine, eCol] = coords;
          const afterStart = line > sLine || (line === sLine && col >= sCol);
          const beforeEnd = line < eLine || (line === eLine && col <= eCol);
          if (afterStart && beforeEnd) {
            return name;
          }
        }
      }
      return null;
    } catch {
      return null;
    }
  }
}

export async function loadLeanAnalyzerBridge(wasmUrlOrBuffer = null) {
  if (!wasmUrlOrBuffer) {
    try {
      const fs = await import("node:fs/promises");
      try {
        const url = new URL("../data/lean_analyzer.wasm", import.meta.url);
        wasmUrlOrBuffer = await fs.readFile(url);
      } catch {
        const url = new URL("../wasm/lean_analyzer.wasm", import.meta.url);
        wasmUrlOrBuffer = await fs.readFile(url);
      }
    } catch {
      return new LeanAnalyzerBridge(null);
    }
  }
  const bytes = wasmUrlOrBuffer instanceof Uint8Array || wasmUrlOrBuffer instanceof ArrayBuffer
    ? wasmUrlOrBuffer
    : await (await fetch(wasmUrlOrBuffer)).arrayBuffer();
  const { instance } = await WebAssembly.instantiate(bytes, {});
  return new LeanAnalyzerBridge(instance);
}

