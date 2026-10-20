// packages/lean-analysis/src/abstract_interpreter.ts
// High-Speed In-Process Abstract Interpreter & WASM Bridge for Lean 4
// Provides offline dataflow analysis, expression lattice abstraction, and zero-process AST evaluation.
// Strict 7-bit ASCII only (INV-001).

/**
 * Abstract values for Lean 4 arithmetic and term evaluations.
 */
export type AbstractSign = "NEGATIVE" | "ZERO" | "POSITIVE" | "NON_NEGATIVE" | "NON_POSITIVE" | "TOP" | "BOTTOM";

export interface IntervalBound {
  min: number;
  max: number;
}

export interface NatCongruence {
  stride: number;
  offset: number;
}

export interface AbstractLatticeState {
  sign: AbstractSign;
  interval?: IntervalBound;
  congruence?: NatCongruence;
  isDeterministic: boolean;
  purity: "PURE" | "IO" | "NON_TERMINATING" | "UNKNOWN";
}

export interface DiagnosticCertificate {
  kind: "NatSubTruncation" | "NatDivModByZero" | "DeadBranch";
  operator: string;
  summary: string;
  hint: string;
}

/**
 * Concrete Syntax Tree (CST) Node representation compatible with Tree-Sitter Lean.
 */
export interface TreeSitterCstNode {
  type: string;
  text?: string;
  children?: TreeSitterCstNode[];
}

function mulNatBound(a: number, b: number): number {
  if (a === 0 || b === 0) return 0;
  return a * b;
}

function gcdNat(a: number, b: number): number {
  let x = Math.abs(Math.trunc(a));
  let y = Math.abs(Math.trunc(b));
  while (y !== 0) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
}

/**
 * Lattice meet, join, partial order, and mutual sign-interval-congruence reduction operations.
 */
export const AbstractLattice = {
  join(a: AbstractSign, b: AbstractSign): AbstractSign {
    if (a === b) return a;
    if (a === "BOTTOM") return b;
    if (b === "BOTTOM") return a;
    if (a === "TOP" || b === "TOP") return "TOP";

    if ((a === "ZERO" && b === "POSITIVE") || (a === "POSITIVE" && b === "ZERO")) return "NON_NEGATIVE";
    if ((a === "ZERO" && b === "NEGATIVE") || (a === "NEGATIVE" && b === "ZERO")) return "NON_POSITIVE";

    if (a === "NON_NEGATIVE" && (b === "ZERO" || b === "POSITIVE")) return "NON_NEGATIVE";
    if (b === "NON_NEGATIVE" && (a === "ZERO" || a === "POSITIVE")) return "NON_NEGATIVE";

    if (a === "NON_POSITIVE" && (b === "ZERO" || b === "NEGATIVE")) return "NON_POSITIVE";
    if (b === "NON_POSITIVE" && (a === "ZERO" || a === "NEGATIVE")) return "NON_POSITIVE";

    return "TOP";
  },

  meet(a: AbstractSign, b: AbstractSign): AbstractSign {
    if (a === b) return a;
    if (a === "TOP") return b;
    if (b === "TOP") return a;
    if (a === "BOTTOM" || b === "BOTTOM") return "BOTTOM";

    if (a === "NON_NEGATIVE" && (b === "POSITIVE" || b === "ZERO")) return b;
    if (b === "NON_NEGATIVE" && (a === "POSITIVE" || a === "ZERO")) return a;

    if (a === "NON_POSITIVE" && (b === "NEGATIVE" || b === "ZERO")) return b;
    if (b === "NON_POSITIVE" && (a === "NEGATIVE" || a === "ZERO")) return a;

    return "BOTTOM";
  },

  isLe(a: AbstractSign, b: AbstractSign): boolean {
    return this.join(a, b) === b;
  },

  signFromInterval(interval: IntervalBound): AbstractSign {
    if (interval.min > interval.max) return "BOTTOM";
    if (interval.min === 0 && interval.max === 0) return "ZERO";
    if (interval.min > 0) return "POSITIVE";
    if (interval.min >= 0) return "NON_NEGATIVE";
    if (interval.max < 0) return "NEGATIVE";
    if (interval.max <= 0) return "NON_POSITIVE";
    return "TOP";
  },

  intervalFromSign(sign: AbstractSign): IntervalBound {
    switch (sign) {
      case "BOTTOM":
        return { min: 1, max: 0 };
      case "ZERO":
        return { min: 0, max: 0 };
      case "POSITIVE":
        return { min: 1, max: Number.POSITIVE_INFINITY };
      case "NON_NEGATIVE":
        return { min: 0, max: Number.POSITIVE_INFINITY };
      case "NEGATIVE":
        return { min: Number.NEGATIVE_INFINITY, max: -1 };
      case "NON_POSITIVE":
        return { min: Number.NEGATIVE_INFINITY, max: 0 };
      case "TOP":
      default:
        return { min: Number.NEGATIVE_INFINITY, max: Number.POSITIVE_INFINITY };
    }
  },

  /**
   * Mutual Granger reduction of interval `[min, max]` and congruence `offset (mod stride)`.
   * Returns `null` if the intersection is empty.
   */
  reduceIntervalCongruence(
    interval: IntervalBound,
    congruence: NatCongruence
  ): { interval: IntervalBound; congruence: NatCongruence } | null {
    if (interval.min > interval.max || interval.max < 0) return null;
    const lo = Math.max(0, Math.trunc(interval.min));
    const hiIsInf = !Number.isFinite(interval.max);
    const hi = hiIsInf ? Number.POSITIVE_INFINITY : Math.max(0, Math.trunc(interval.max));
    const s = Math.max(0, Math.trunc(congruence.stride));
    const o = s === 0 ? Math.max(0, Math.trunc(congruence.offset)) : ((Math.trunc(congruence.offset) % s) + s) % s;

    if (s === 0) {
      if (o < lo || (!hiIsInf && o > hi)) return null;
      return {
        interval: { min: o, max: o },
        congruence: { stride: 0, offset: o }
      };
    }

    const loRem = lo % s;
    const deltaLo = o >= loRem ? o - loRem : s - (loRem - o);
    const newLo = lo + deltaLo;
    if (!hiIsInf && newLo > hi) return null;

    let newHi = Number.POSITIVE_INFINITY;
    if (!hiIsInf) {
      const hiRem = hi % s;
      const deltaHi = hiRem >= o ? hiRem - o : s - (o - hiRem);
      if (hi < deltaHi) return null;
      newHi = hi - deltaHi;
      if (newHi < newLo) return null;
    }

    const tightenedCg: NatCongruence =
      newLo === newHi && Number.isFinite(newHi)
        ? { stride: 0, offset: newLo }
        : { stride: s, offset: o };
    return {
      interval: { min: newLo, max: newHi },
      congruence: tightenedCg
    };
  },

  reduceState(state: AbstractLatticeState): AbstractLatticeState {
    if (state.sign === "BOTTOM") {
      return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
    }

    if (state.interval) {
      if (state.interval.min > state.interval.max) {
        return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
      }
      const signInterval = this.intervalFromSign(state.sign);
      const min = Math.max(state.interval.min, signInterval.min);
      const max = Math.min(state.interval.max, signInterval.max);
      if (min > max) {
        return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
      }
      let reducedInterval: IntervalBound = { min, max };
      let reducedCongruence = state.congruence;
      if (reducedCongruence && reducedInterval.min >= 0) {
        const granger = this.reduceIntervalCongruence(reducedInterval, reducedCongruence);
        if (!granger) {
          return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
        }
        reducedInterval = granger.interval;
        reducedCongruence = granger.congruence;
      } else if (reducedInterval.min === reducedInterval.max && Number.isFinite(reducedInterval.min) && reducedInterval.min >= 0) {
        reducedCongruence = { stride: 0, offset: reducedInterval.min };
      }
      const intervalSign = this.signFromInterval(reducedInterval);
      const reducedSign = this.meet(state.sign, intervalSign);
      if (reducedSign === "BOTTOM") {
        return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
      }
      return {
        ...state,
        sign: reducedSign,
        interval: reducedInterval,
        congruence: reducedCongruence
      };
    }

    if (state.sign === "ZERO") {
      return {
        ...state,
        interval: { min: 0, max: 0 },
        congruence: { stride: 0, offset: 0 }
      };
    }

    return { ...state };
  },

  isStateLe(a: AbstractLatticeState, b: AbstractLatticeState): boolean {
    const ra = this.reduceState(a);
    const rb = this.reduceState(b);
    if (ra.sign === "BOTTOM") return true;
    if (!this.isLe(ra.sign, rb.sign)) return false;
    if (rb.interval) {
      if (!ra.interval) return false;
      if (ra.interval.min < rb.interval.min || ra.interval.max > rb.interval.max) {
        return false;
      }
    }
    return true;
  },

  widenInterval(prev: IntervalBound, next: IntervalBound, isNat = false): IntervalBound {
    if (prev.min > prev.max) return { ...next };
    if (next.min > next.max) return { ...prev };
    const rawMin = next.min < prev.min ? (isNat ? 0 : Number.NEGATIVE_INFINITY) : prev.min;
    const min = isNat ? Math.max(0, rawMin) : rawMin;
    const max = next.max > prev.max ? Number.POSITIVE_INFINITY : prev.max;
    return { min, max };
  },

  widenIntervalWithThresholds(
    prev: IntervalBound,
    next: IntervalBound,
    thresholds: number[],
    isNat = true
  ): IntervalBound {
    if (prev.min > prev.max) return { ...next };
    if (next.min > next.max) return { ...prev };
    const sorted = [...thresholds].sort((a, b) => a - b);
    let min = prev.min;
    if (next.min < prev.min) {
      const lower = [...sorted].reverse().find((t) => t <= next.min);
      min = lower !== undefined ? lower : (isNat ? 0 : Number.NEGATIVE_INFINITY);
    }
    if (isNat) min = Math.max(0, min);

    let max = prev.max;
    if (next.max > prev.max) {
      const upper = sorted.find((t) => t >= next.max);
      max = upper !== undefined ? upper : Number.POSITIVE_INFINITY;
    }
    return { min, max };
  },

  narrowInterval(wide: IntervalBound, refined: IntervalBound, isNat = false): IntervalBound {
    if (wide.min > wide.max) return { ...wide };
    if (refined.min > refined.max) return { ...refined };
    const rawMin = wide.min === Number.NEGATIVE_INFINITY ? refined.min : Math.max(wide.min, refined.min);
    const min = isNat ? Math.max(0, rawMin) : rawMin;
    const max = wide.max === Number.POSITIVE_INFINITY ? refined.max : Math.min(wide.max, refined.max);
    return { min, max };
  }
};

/**
 * In-process abstract interpreter evaluating Lean 4 declarations without spawning lake serve.
 */
export class LeanAbstractInterpreter {
  private declarations: Map<string, AbstractLatticeState> = new Map();
  private wasmModule: any = null;

  constructor(wasmModuleInstance?: any) {
    this.wasmModule = wasmModuleInstance || null;
  }

  /**
   * Initializes or attaches a WASM accelerated evaluation engine.
   * @param wasmBytes - Binary WASM buffer compiled from crates/lean-analyzer.
   */
  public async loadWasmEngine(wasmBytes: Uint8Array): Promise<boolean> {
    try {
      const wasm = (globalThis as any).WebAssembly;
      if (typeof wasm !== "undefined") {
        const { instance } = await wasm.instantiate(wasmBytes, {});
        this.wasmModule = instance.exports;
        return true;
      }
      return false;
    } catch (_err) {
      return false;
    }
  }

  private callWasmIntervalOp(
    fnName: string,
    l: IntervalBound,
    r: IntervalBound
  ): IntervalBound | null {
    if (
      this.wasmModule &&
      typeof this.wasmModule[fnName] === "function" &&
      this.wasmModule.memory &&
      typeof this.wasmModule.lean_analyzer_get_scratch_ptr === "function" &&
      Number.isFinite(l.min) &&
      Number.isFinite(l.max) &&
      Number.isFinite(r.min) &&
      Number.isFinite(r.max)
    ) {
      const ptr = this.wasmModule.lean_analyzer_get_scratch_ptr();
      const ok = this.wasmModule[fnName](
        BigInt(Math.trunc(l.min)),
        BigInt(Math.trunc(l.max)),
        BigInt(Math.trunc(r.min)),
        BigInt(Math.trunc(r.max)),
        ptr
      );
      if (ok === 1) {
        const view = new BigInt64Array(this.wasmModule.memory.buffer, ptr, 2);
        const MAX_I64 = 9223372036854775807n;
        return {
          min: view[0] >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(view[0]),
          max: view[1] >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(view[1])
        };
      }
    }
    return null;
  }

  /**
   * Mutual sign-interval-congruence domain reduction (WASM-accelerated when loaded).
   */
  public reduceState(state: AbstractLatticeState): AbstractLatticeState {
    if (
      state.interval &&
      state.congruence &&
      this.wasmModule &&
      typeof this.wasmModule.lean_analyzer_reduce_interval_congruence === "function" &&
      this.wasmModule.memory &&
      typeof this.wasmModule.lean_analyzer_get_scratch_ptr === "function" &&
      Number.isFinite(state.interval.min) &&
      Number.isFinite(state.interval.max) &&
      state.interval.min >= 0
    ) {
      const ptr = this.wasmModule.lean_analyzer_get_scratch_ptr();
      const ok = this.wasmModule.lean_analyzer_reduce_interval_congruence(
        BigInt(Math.trunc(state.interval.min)),
        BigInt(Math.trunc(state.interval.max)),
        BigInt(Math.max(0, Math.trunc(state.congruence.stride))),
        BigInt(Math.max(0, Math.trunc(state.congruence.offset))),
        ptr
      );
      if (ok === 0) {
        return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
      }
      const view = new BigInt64Array(this.wasmModule.memory.buffer, ptr, 4);
      return AbstractLattice.reduceState({
        ...state,
        interval: { min: Number(view[0]), max: Number(view[1]) },
        congruence: { stride: Number(view[2]), offset: Number(view[3]) }
      });
    }
    return AbstractLattice.reduceState(state);
  }

  /**
   * Discharges Lean 4 termination obligation `n - (i + step) < n - i` under guard `i - n <= guardDiff`
   * using the Zone DBM domain (WASM-accelerated when loaded).
   */
  public checkZoneSubDecreasing(guardDiff: number, step: number): "BOTTOM" | "FALSE" | "TRUE" | "TOP" {
    if (
      this.wasmModule &&
      typeof this.wasmModule.lean_analyzer_zone_check_sub_decreasing === "function"
    ) {
      const code = this.wasmModule.lean_analyzer_zone_check_sub_decreasing(
        BigInt(Math.trunc(guardDiff)),
        BigInt(Math.trunc(step))
      );
      if (code === 0) return "BOTTOM";
      if (code === 1) return "FALSE";
      if (code === 2) return "TRUE";
      return "TOP";
    }
    if (step <= 0) return "FALSE";
    if (guardDiff <= -1) return "TRUE";
    return "TOP";
  }

  private evalBinaryNatOp(
    op: string,
    leftRaw: AbstractLatticeState,
    rightRaw: AbstractLatticeState
  ): AbstractLatticeState | null {
    const left = this.reduceState(leftRaw);
    const right = this.reduceState(rightRaw);

    if (left.sign === "BOTTOM" || right.sign === "BOTTOM") {
      return {
        sign: "BOTTOM",
        interval: undefined,
        isDeterministic: left.isDeterministic && right.isDeterministic,
        purity: "PURE"
      };
    }

    const l = left.interval
      ? { min: Math.max(0, left.interval.min), max: Math.max(0, left.interval.max) }
      : undefined;
    const r = right.interval
      ? { min: Math.max(0, right.interval.min), max: Math.max(0, right.interval.max) }
      : undefined;

    let sign: AbstractSign = "NON_NEGATIVE";
    let interval: IntervalBound | undefined = undefined;
    let congruence: NatCongruence | undefined = undefined;

    if (op === "Nat.add" || op === "+" || op === "HAdd.hAdd") {
      if (left.sign === "POSITIVE" || right.sign === "POSITIVE") {
        sign = "POSITIVE";
      } else if (left.sign === "ZERO" && right.sign === "ZERO") {
        sign = "ZERO";
      }
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_add", l, r) || {
          min: l.min + r.min,
          max: l.max + r.max
        };
      }
      if (left.congruence && right.congruence) {
        const g = gcdNat(left.congruence.stride, right.congruence.stride);
        const off = left.congruence.offset + right.congruence.offset;
        congruence = { stride: g, offset: g === 0 ? off : off % g };
      }
    } else if (op === "Nat.sub" || op === "-" || op === "HSub.hSub") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_sub", l, r) || {
          min: Math.max(0, l.min - r.max),
          max: Math.max(0, l.max - r.min)
        };
      }
    } else if (op === "Nat.mul" || op === "*" || op === "HMul.hMul") {
      if (left.sign === "ZERO" || right.sign === "ZERO") {
        sign = "ZERO";
      } else if (left.sign === "POSITIVE" && right.sign === "POSITIVE") {
        sign = "POSITIVE";
      } else {
        sign = "NON_NEGATIVE";
      }
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_mul", l, r) || {
          min: mulNatBound(l.min, r.min),
          max: mulNatBound(l.max, r.max)
        };
      }
      if (left.congruence && right.congruence) {
        const s1 = left.congruence.stride;
        const o1 = left.congruence.offset;
        const s2 = right.congruence.stride;
        const o2 = right.congruence.offset;
        const g = gcdNat(s1 * s2, gcdNat(s1 * o2, s2 * o1));
        const off = o1 * o2;
        congruence = { stride: g, offset: g === 0 ? off : off % g };
      }
    } else if (op === "Nat.div" || op === "/" || op === "HDiv.hDiv") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_div", l, r) || undefined;
        if (!interval) {
          if (r.min === 0 && r.max === 0) {
            interval = { min: 0, max: 0 };
          } else if (r.min === 0) {
            interval = { min: 0, max: l.max };
          } else {
            const minQuot = r.max === Number.POSITIVE_INFINITY ? 0 : Math.floor(l.min / r.max);
            const maxQuot = Math.floor(l.max / r.min);
            interval = { min: minQuot, max: maxQuot };
          }
        }
      }
    } else if (op === "Nat.mod" || op === "%" || op === "HMod.hMod") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_mod", l, r) || undefined;
        if (!interval) {
          if (r.min === 0 && r.max === 0) {
            interval = { min: l.min, max: l.max };
          } else if (r.min === 0) {
            const boundFromDivisor = r.max === Number.POSITIVE_INFINITY
              ? Number.POSITIVE_INFINITY
              : Math.max(0, r.max - 1);
            interval = {
              min: 0,
              max: Math.max(l.max, boundFromDivisor)
            };
          } else if (
            r.min === r.max &&
            Number.isFinite(l.max) &&
            Number.isFinite(r.min) &&
            Math.floor(l.min / r.min) === Math.floor(l.max / r.min)
          ) {
            interval = {
              min: l.min % r.min,
              max: l.max % r.min
            };
          } else {
            const maxRem = r.max === Number.POSITIVE_INFINITY
              ? l.max
              : Math.min(l.max, Math.max(0, r.max - 1));
            interval = {
              min: 0,
              max: maxRem
            };
          }
        }
      }
    } else if (op === "Nat.pow" || op === "^" || op === "HPow.hPow") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_pow", l, r) || {
          min: r.max === 0 ? 1 : Math.pow(l.min, r.min),
          max: r.max === 0 ? 1 : Math.pow(l.max, r.max)
        };
      }
    } else if (op === "Nat.land" || op === "&&&" || op === "AndOp.and" || op === "HAnd.hAnd") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_land", l, r) || {
          min: l.min === l.max && r.min === r.max ? Number(BigInt(l.min) & BigInt(r.min)) : 0,
          max: Math.min(l.max, r.max)
        };
      }
    } else if (op === "Nat.lor" || op === "|||" || op === "OrOp.or" || op === "HOr.hOr") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_lor", l, r) || undefined;
        if (!interval) {
          if (l.min === l.max && r.min === r.max && Number.isFinite(l.min) && Number.isFinite(r.min)) {
            const v = Number(BigInt(l.min) | BigInt(r.min));
            interval = { min: v, max: v };
          } else {
            const maxIn = Math.max(l.max, r.max);
            let mask = 1;
            while (mask <= maxIn && Number.isFinite(maxIn)) mask *= 2;
            interval = { min: Math.max(l.min, r.min), max: Number.isFinite(maxIn) ? mask - 1 : Number.POSITIVE_INFINITY };
          }
        }
      }
    } else if (op === "Nat.xor" || op === "^^^" || op === "XorOp.xor" || op === "HXor.hXor") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_xor", l, r) || undefined;
        if (!interval) {
          if (l.min === l.max && r.min === r.max && Number.isFinite(l.min) && Number.isFinite(r.min)) {
            const v = Number(BigInt(l.min) ^ BigInt(r.min));
            interval = { min: v, max: v };
          } else {
            const maxIn = Math.max(l.max, r.max);
            let mask = 1;
            while (mask <= maxIn && Number.isFinite(maxIn)) mask *= 2;
            interval = { min: 0, max: Number.isFinite(maxIn) ? mask - 1 : Number.POSITIVE_INFINITY };
          }
        }
      }
    } else if (op === "Nat.shiftLeft" || op === "<<<" || op === "HShiftLeft.hShiftLeft") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_shl", l, r) || {
          min: l.min * Math.pow(2, r.min),
          max: l.max * Math.pow(2, r.max)
        };
      }
    } else if (op === "Nat.shiftRight" || op === ">>>" || op === "HShiftRight.hShiftRight") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = this.callWasmIntervalOp("lean_analyzer_eval_nat_shr", l, r) || {
          min: Math.floor(l.min / Math.pow(2, r.max)),
          max: Math.floor(l.max / Math.pow(2, r.min))
        };
      }
    } else if (op === "Nat.min" || op === "min") {
      if (left.sign === "ZERO" || right.sign === "ZERO") {
        sign = "ZERO";
      } else if (left.sign === "POSITIVE" && right.sign === "POSITIVE") {
        sign = "POSITIVE";
      } else {
        sign = "NON_NEGATIVE";
      }
      if (l && r) {
        interval = {
          min: Math.min(l.min, r.min),
          max: Math.min(l.max, r.max)
        };
      }
    } else if (op === "Nat.max" || op === "max") {
      if (left.sign === "POSITIVE" || right.sign === "POSITIVE") {
        sign = "POSITIVE";
      } else if (left.sign === "ZERO" && right.sign === "ZERO") {
        sign = "ZERO";
      } else {
        sign = "NON_NEGATIVE";
      }
      if (l && r) {
        interval = {
          min: Math.max(l.min, r.min),
          max: Math.max(l.max, r.max)
        };
      }
    } else {
      return null;
    }

    return this.reduceState({
      sign,
      interval,
      congruence,
      isDeterministic: left.isDeterministic && right.isDeterministic,
      purity: "PURE"
    });
  }

  /**
   * Analyzes an integer or Nat expression AST node into its abstract lattice bounds.
   */
  public evalExpr(expr: { op?: string, args?: any[], value?: number }): AbstractLatticeState {
    if (expr.value !== undefined) {
      const v = expr.value;
      const sign: AbstractSign = v > 0 ? "POSITIVE" : (v === 0 ? "ZERO" : "NEGATIVE");
      return this.reduceState({
        sign,
        interval: { min: v, max: v },
        congruence: v >= 0 ? { stride: 0, offset: v } : undefined,
        isDeterministic: true,
        purity: "PURE"
      });
    }

    if (expr.op && expr.args && expr.args.length === 1) {
      const arg = this.evalExpr(expr.args[0]);
      if (expr.op === "Nat.succ") {
        return this.evalBinaryNatOp("Nat.add", arg, this.evalExpr({ value: 1 }))!;
      }
      if (expr.op === "Nat.pred") {
        return this.evalBinaryNatOp("Nat.sub", arg, this.evalExpr({ value: 1 }))!;
      }
    }

    if (expr.op && expr.args && expr.args.length === 2) {
      const left = this.evalExpr(expr.args[0]);
      const right = this.evalExpr(expr.args[1]);
      const res = this.evalBinaryNatOp(expr.op, left, right);
      if (res !== null) {
        return res;
      }
    }

    // Default top / conservative bound
    return {
      sign: "TOP",
      isDeterministic: false,
      purity: "UNKNOWN"
    };
  }

  /**
   * Directly evaluates a Tree-Sitter Concrete Syntax Tree (CST) node without invoking Lean subprocess.
   */
  public evalCstNode(node: TreeSitterCstNode): AbstractLatticeState {
    // Number literal node
    if (node.type === "number" || node.type === "nat_lit") {
      const val = parseInt(node.text || "0", 10);
      if (!isNaN(val)) {
        return this.reduceState({
          sign: val > 0 ? "POSITIVE" : (val === 0 ? "ZERO" : "NEGATIVE"),
          interval: { min: val, max: val },
          congruence: val >= 0 ? { stride: 0, offset: val } : undefined,
          isDeterministic: true,
          purity: "PURE"
        });
      }
    }

    // Application node: (f arg1 arg2)
    if (node.type === "apply_expression" && node.children && node.children.length >= 3) {
      const fnNode = node.children[0];
      const fnName = fnNode.text || "";
      const left = this.evalCstNode(node.children[1]);
      const right = this.evalCstNode(node.children[2]);
      const res = this.evalBinaryNatOp(fnName, left, right);
      if (res !== null) {
        return res;
      }
    }

    // Default top / conservative bound
    return {
      sign: "TOP",
      isDeterministic: false,
      purity: "UNKNOWN"
    };
  }

  /**
   * Widens two abstract lattice states (using Nat-aware widening when both states are non-negative).
   */
  public widen(prevRaw: AbstractLatticeState, nextRaw: AbstractLatticeState, thresholds?: number[]): AbstractLatticeState {
    const prev = this.reduceState(prevRaw);
    const next = this.reduceState(nextRaw);
    if (prev.sign === "BOTTOM") return next;
    if (next.sign === "BOTTOM") return prev;

    const isNat =
      AbstractLattice.isLe(prev.sign, "NON_NEGATIVE") &&
      AbstractLattice.isLe(next.sign, "NON_NEGATIVE");
    const joinedSign = AbstractLattice.join(prev.sign, next.sign);
    const interval =
      prev.interval && next.interval
        ? (thresholds && thresholds.length > 0
            ? AbstractLattice.widenIntervalWithThresholds(prev.interval, next.interval, thresholds, isNat)
            : AbstractLattice.widenInterval(prev.interval, next.interval, isNat))
        : undefined;

    return this.reduceState({
      sign: joinedSign,
      interval,
      isDeterministic: prev.isDeterministic && next.isDeterministic,
      purity: prev.purity === next.purity ? prev.purity : "UNKNOWN"
    });
  }

  /**
   * Narrows a widened post-fixpoint abstract lattice state using a subsequent transfer evaluation.
   */
  public narrow(wideRaw: AbstractLatticeState, refinedRaw: AbstractLatticeState): AbstractLatticeState {
    const wide = this.reduceState(wideRaw);
    const refined = this.reduceState(refinedRaw);
    if (wide.sign === "BOTTOM") return wide;
    if (refined.sign === "BOTTOM") return refined;

    const isNat =
      AbstractLattice.isLe(wide.sign, "NON_NEGATIVE") &&
      AbstractLattice.isLe(refined.sign, "NON_NEGATIVE");
    const metSign = AbstractLattice.meet(wide.sign, refined.sign);
    const interval =
      wide.interval && refined.interval
        ? AbstractLattice.narrowInterval(wide.interval, refined.interval, isNat)
        : wide.interval || refined.interval;

    return this.reduceState({
      sign: metSign,
      interval,
      isDeterministic: wide.isDeterministic && refined.isDeterministic,
      purity: wide.purity
    });
  }

  /**
   * Computes a fixpoint over recursive step equations using monotone join.
   */
  public computeFixpoint(
    init: AbstractLatticeState,
    transferFn: (curr: AbstractLatticeState) => AbstractLatticeState,
    maxIterations = 20
  ): AbstractLatticeState {
    let curr = this.reduceState(init);
    for (let iter = 0; iter < maxIterations; iter++) {
      const next = this.reduceState(transferFn(curr));
      if (AbstractLattice.isStateLe(next, curr)) {
        return curr; // Post-fixpoint reached
      }
      curr = this.reduceState({
        sign: AbstractLattice.join(curr.sign, next.sign),
        interval: curr.interval && next.interval ? {
          min: Math.min(curr.interval.min, next.interval.min),
          max: Math.max(curr.interval.max, next.interval.max)
        } : undefined,
        isDeterministic: curr.isDeterministic && next.isDeterministic,
        purity: curr.purity
      });
    }
    return curr;
  }

  /**
   * Computes a sound post-fixpoint using Cousot-Cousot widening (optionally stepped through `thresholds`)
   * followed by narrowing.
   */
  public computeWideningFixpoint(
    init: AbstractLatticeState,
    transferFn: (curr: AbstractLatticeState) => AbstractLatticeState,
    maxIterations = 20,
    thresholds?: number[]
  ): AbstractLatticeState {
    let curr = this.reduceState(init);
    for (let iter = 0; iter < maxIterations; iter++) {
      const next = this.reduceState(transferFn(curr));
      if (AbstractLattice.isStateLe(next, curr)) {
        const post = this.reduceState(transferFn(curr));
        return this.narrow(curr, post);
      }
      curr = this.widen(curr, next, thresholds);
    }
    const post = this.reduceState(transferFn(curr));
    return this.narrow(curr, post);
  }

  /**
   * Evaluates an expression and collects actionable static diagnostic certificates
   * for Nat subtraction truncation (`[a, b] - [c, d]` where `b <= c` and `c > 0`)
   * and Nat division/modulo where the divisor interval includes `0`.
   */
  public diagnoseExpr(expr: { op?: string; args?: any[]; value?: number }): {
    state: AbstractLatticeState;
    certificates: DiagnosticCertificate[];
  } {
    const certificates: DiagnosticCertificate[] = [];
    const visit = (node: { op?: string; args?: any[]; value?: number }): void => {
      if (!node || !node.op || !node.args) return;
      for (const child of node.args) {
        visit(child);
      }
      if (node.args.length === 2) {
        const l = this.evalExpr(node.args[0]);
        const r = this.evalExpr(node.args[1]);
        if (l.interval && r.interval) {
          const op = node.op;
          if (op === "Nat.sub" || op === "-") {
            if (l.interval.max <= r.interval.min && r.interval.min > 0) {
              certificates.push({
                kind: "NatSubTruncation",
                operator: op,
                summary: `Natural subtraction \`${op}\` on [${l.interval.min}, ${l.interval.max}] - [${r.interval.min}, ${r.interval.max}] saturates to [0, 0].`,
                hint: "Add guard `b <= a` or switch to `Int` subtraction if negative values are intended."
              });
            }
          } else if (op === "Nat.div" || op === "/" || op === "Nat.mod" || op === "%") {
            if (r.interval.min <= 0 && 0 <= r.interval.max) {
              certificates.push({
                kind: "NatDivModByZero",
                operator: op,
                summary: `Divisor interval [${r.interval.min}, ${r.interval.max}] in \`${op}\` includes 0 (Lean total semantics: a / 0 = 0, a % 0 = a).`,
                hint: "Prove `0 < divisor` or guard against zero divisor."
              });
            }
          }
        }
      }
    };
    visit(expr);
    return {
      state: this.evalExpr(expr),
      certificates
    };
  }
}

