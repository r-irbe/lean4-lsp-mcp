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

/**
 * Lattice meet and join operations.
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
   * Analyzes an integer or Nat expression AST node into its abstract lattice bounds.
   */
  public evalExpr(expr: { op?: string, args?: any[], value?: number }): AbstractLatticeState {
    if (expr.value !== undefined) {
      const v = expr.value;
      const sign: AbstractSign = v > 0 ? "POSITIVE" : (v === 0 ? "ZERO" : "NEGATIVE");
      return {
        sign,
        interval: { min: v, max: v },
        isDeterministic: true,
        purity: "PURE"
      };
    }

    if (expr.op === "Nat.add" && expr.args && expr.args.length === 2) {
      const left = this.evalExpr(expr.args[0]);
      const right = this.evalExpr(expr.args[1]);

      let sign: AbstractSign = "NON_NEGATIVE";
      if (left.sign === "POSITIVE" || right.sign === "POSITIVE") {
        sign = "POSITIVE";
      }

      let interval: IntervalBound | undefined = undefined;
      if (left.interval && right.interval) {
        interval = {
          min: left.interval.min + right.interval.min,
          max: left.interval.max + right.interval.max
        };
      }

      return {
        sign,
        interval,
        isDeterministic: left.isDeterministic && right.isDeterministic,
        purity: "PURE"
      };
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
        return {
          sign: val > 0 ? "POSITIVE" : (val === 0 ? "ZERO" : "NEGATIVE"),
          interval: { min: val, max: val },
          isDeterministic: true,
          purity: "PURE"
        };
      }
    }

    // Application node: (f arg1 arg2)
    if (node.type === "apply_expression" && node.children && node.children.length >= 2) {
      const fnNode = node.children[0];
      const fnName = fnNode.text || "";

      if ((fnName === "Nat.add" || fnName === "+") && node.children.length >= 3) {
        const left = this.evalCstNode(node.children[1]);
        const right = this.evalCstNode(node.children[2]);

        let sign: AbstractSign = "NON_NEGATIVE";
        if (left.sign === "POSITIVE" || right.sign === "POSITIVE") {
          sign = "POSITIVE";
        }

        let interval: IntervalBound | undefined = undefined;
        if (left.interval && right.interval) {
          interval = {
            min: left.interval.min + right.interval.min,
            max: left.interval.max + right.interval.max
          };
        }

        return {
          sign,
          interval,
          isDeterministic: left.isDeterministic && right.isDeterministic,
          purity: "PURE"
        };
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
   * Computes a fixpoint over recursive step equations.
   */
  public computeFixpoint(
    init: AbstractLatticeState,
    transferFn: (curr: AbstractLatticeState) => AbstractLatticeState,
    maxIterations = 20
  ): AbstractLatticeState {
    let curr = init;
    for (let iter = 0; iter < maxIterations; iter++) {
      const next = transferFn(curr);
      if (next.sign === curr.sign &&
          next.interval?.min === curr.interval?.min &&
          next.interval?.max === curr.interval?.max) {
        return curr; // Fixpoint reached
      }
      curr = {
        sign: AbstractLattice.join(curr.sign, next.sign),
        interval: curr.interval && next.interval ? {
          min: Math.min(curr.interval.min, next.interval.min),
          max: Math.max(curr.interval.max, next.interval.max)
        } : undefined,
        isDeterministic: curr.isDeterministic && next.isDeterministic,
        purity: curr.purity
      };
    }
    return curr;
  }
}
