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

export interface AbstractLatticeState {
  sign: AbstractSign;
  interval?: IntervalBound;
  isDeterministic: boolean;
  purity: "PURE" | "IO" | "NON_TERMINATING" | "UNKNOWN";
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

/**
 * Lattice meet, join, partial order, and mutual sign-interval reduction operations.
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

  reduceState(state: AbstractLatticeState): AbstractLatticeState {
    if (state.sign === "BOTTOM") {
      return { ...state, sign: "BOTTOM", interval: undefined };
    }

    if (state.interval) {
      if (state.interval.min > state.interval.max) {
        return { ...state, sign: "BOTTOM", interval: undefined };
      }
      const signInterval = this.intervalFromSign(state.sign);
      const min = Math.max(state.interval.min, signInterval.min);
      const max = Math.min(state.interval.max, signInterval.max);
      if (min > max) {
        return { ...state, sign: "BOTTOM", interval: undefined };
      }
      const reducedInterval: IntervalBound = { min, max };
      const intervalSign = this.signFromInterval(reducedInterval);
      const reducedSign = this.meet(state.sign, intervalSign);
      if (reducedSign === "BOTTOM") {
        return { ...state, sign: "BOTTOM", interval: undefined };
      }
      return {
        ...state,
        sign: reducedSign,
        interval: reducedInterval
      };
    }

    if (state.sign === "ZERO") {
      return {
        ...state,
        interval: { min: 0, max: 0 }
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
   * @param wasmBytes - Binary WASM buffer compiled from Lean 4 C99 kernel.
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

  /**
   * Mutual sign-interval domain reduction.
   */
  public reduceState(state: AbstractLatticeState): AbstractLatticeState {
    return AbstractLattice.reduceState(state);
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

    if (op === "Nat.add" || op === "+") {
      if (left.sign === "POSITIVE" || right.sign === "POSITIVE") {
        sign = "POSITIVE";
      } else if (left.sign === "ZERO" && right.sign === "ZERO") {
        sign = "ZERO";
      }
      if (l && r) {
        interval = {
          min: l.min + r.min,
          max: l.max + r.max
        };
      }
    } else if (op === "Nat.sub" || op === "-") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        interval = {
          min: Math.max(0, l.min - r.max),
          max: Math.max(0, l.max - r.min)
        };
      }
    } else if (op === "Nat.mul" || op === "*") {
      if (left.sign === "ZERO" || right.sign === "ZERO") {
        sign = "ZERO";
      } else if (left.sign === "POSITIVE" && right.sign === "POSITIVE") {
        sign = "POSITIVE";
      } else {
        sign = "NON_NEGATIVE";
      }
      if (l && r) {
        interval = {
          min: mulNatBound(l.min, r.min),
          max: mulNatBound(l.max, r.max)
        };
      }
    } else if (op === "Nat.div" || op === "/") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        if (r.min === 0 && r.max === 0) {
          // Lean 4 total division: n / 0 = 0
          interval = { min: 0, max: 0 };
        } else if (r.min === 0) {
          // Divisor interval contains both 0 and >= 1
          interval = { min: 0, max: l.max };
        } else {
          const minQuot = r.max === Number.POSITIVE_INFINITY ? 0 : Math.floor(l.min / r.max);
          const maxQuot = Math.floor(l.max / r.min);
          interval = { min: minQuot, max: maxQuot };
        }
      }
    } else if (op === "Nat.mod" || op === "%") {
      sign = "NON_NEGATIVE";
      if (l && r) {
        if (r.min === 0 && r.max === 0) {
          // Lean 4 total modulo: n % 0 = n
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
          // Single quotient bucket: exact remainder interval
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
        isDeterministic: true,
        purity: "PURE"
      });
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
  public widen(prevRaw: AbstractLatticeState, nextRaw: AbstractLatticeState): AbstractLatticeState {
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
        ? AbstractLattice.widenInterval(prev.interval, next.interval, isNat)
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
   * Computes a sound post-fixpoint using Cousot-Cousot widening followed by narrowing.
   */
  public computeWideningFixpoint(
    init: AbstractLatticeState,
    transferFn: (curr: AbstractLatticeState) => AbstractLatticeState,
    maxIterations = 20
  ): AbstractLatticeState {
    let curr = this.reduceState(init);
    for (let iter = 0; iter < maxIterations; iter++) {
      const next = this.reduceState(transferFn(curr));
      if (AbstractLattice.isStateLe(next, curr)) {
        const post = this.reduceState(transferFn(curr));
        return this.narrow(curr, post);
      }
      curr = this.widen(curr, next);
    }
    const post = this.reduceState(transferFn(curr));
    return this.narrow(curr, post);
  }
}
