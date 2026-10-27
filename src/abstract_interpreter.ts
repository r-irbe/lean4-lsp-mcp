// packages/lean-analysis/src/abstract_interpreter.ts
// High-Speed In-Process Abstract Interpreter & WASM Bridge for Lean 4
// Provides offline dataflow analysis, expression lattice abstraction, and zero-process AST evaluation.
// Strict 7-bit ASCII only (INV-001).

import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

export interface WasmInstanceLike {
  exports: Record<string, any>;
}

let defaultWasmInstance: WasmInstanceLike | null | undefined = undefined;

export function getDefaultWasmInstance(): WasmInstanceLike | null {
  if (defaultWasmInstance !== undefined) {
    return defaultWasmInstance;
  }
  defaultWasmInstance = null;
  try {
    const wasm = (globalThis as any).WebAssembly;
    if (typeof wasm !== "undefined") {
      const candidates = [
        path.resolve(__dirname, "../data/lean_analyzer.wasm"),
        path.resolve(__dirname, "../../data/lean_analyzer.wasm"),
      ];
      for (const wasmPath of candidates) {
        if (fs.existsSync(wasmPath)) {
          const bytes = fs.readFileSync(wasmPath);
          const mod = new wasm.Module(bytes);
          defaultWasmInstance = new wasm.Instance(mod, {});
          break;
        }
      }
    }
  } catch {
    defaultWasmInstance = null;
  }
  return defaultWasmInstance ?? null;
}

/**
 * Abstract values for Lean 4 arithmetic and term evaluations.
 */
export type AbstractSign =
  | "NEGATIVE"
  | "ZERO"
  | "POSITIVE"
  | "NON_NEGATIVE"
  | "NON_POSITIVE"
  | "TOP"
  | "BOTTOM";

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

export type DiagnosticKind =
  | "NatSubTruncation"
  | "NatDivModByZero"
  | "DeadBranch"
  | "ZoneTerminationCert"
  | "HypothesisEcho"
  | "ReflexiveTautology"
  | "NatNonnegTriviality"
  | "UnusedUnderscoreBinder"
  | "MisalignedDocstring"
  | "OneWayBoolChecker"
  | "OverConcreteFixedArity"
  | "SairLaw01LetZetaTax"
  | "SairLaw01bDagSharing"
  | "SairLaw01cSiblingWhnfCse"
  | "SairLaw02ClosedSubtreeHoist"
  | "SairLaw02bInnerBinderOrder"
  | "SairLaw03ConstantLeftOp"
  | "SairLaw03bConstantLeftPow2Mask"
  | "SairLaw04PointFreeEtaWrapper"
  | "SairLaw05SharedAbbrevMotive"
  | "KernelBrecOnTax"
  | "SairLaw07CsimpDualPath"
  | "SairLaw08BoolRecOverIte"
  | "SairLaw09UnboxedProductSpine"
  | "SairLaw10CpsPairElim"
  | "SairLaw11InductivePreHoist"
  | "SairLaw12DirectNatRecSign"
  | "SairLaw12bUnboxedQuotientSignDiff"
  | "SairLaw13MultiLimbSquare"
  | "SairLaw13bSingleLimbSquare"
  | "KernelPowerOfTwoDivMod"
  | "SairLaw14bGmpHornerAsymmetry"
  | "SairLaw14cBitwiseSubpipeline"
  | "SairLaw15SwarWordPacking"
  | "SairLaw16FixedTripUnroll"
  | "SairLaw16bGmpLimbAlignment"
  | "SairLaw17CbvStateCanonical"
  | "SairLaw18FrontierZddMask"
  | "SairLaw18bSingleBitPopcount"
  | "SairLaw19CombinedLookaheadGuard"
  | "SairLaw19bZeroMaskPrune"
  | "SairLaw20AnfZhegalkinRotation"
  | "SairLaw21HeuristicListPerm"
  | "SairLaw22ZeroPropRuntimeCone"
  | "SairLaw22bHotColdSeparation"
  | "SairLaw22cNamedRecursorBinders"
  | "SairLaw23ZeroTypeclassHotCone"
  | "SairLaw24OptimalCpsArity"
  | "SairLaw25ModuleHeaderHumanization"
  | "SairLaw25bAbbrevLiteralExtraction"
  | "AltProofRouteCandidate";

export interface CodeReplacement {
  title: string;
  range: [number, number, number, number];
  newText: string;
  isPreferred: boolean;
}

export interface DiagnosticCertificate {
  kind: DiagnosticKind;
  code?: string;
  severity?: number;
  range?: [number, number, number, number];
  operator: string;
  summary: string;
  hint: string;
  altproofRoute?: string;
  quickfix?: CodeReplacement;
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
    const o =
      s === 0
        ? Math.max(0, Math.trunc(congruence.offset))
        : ((Math.trunc(congruence.offset) % s) + s) % s;

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

    const tightenedCg =
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
      let reducedCongruence: NatCongruence | undefined = state.congruence;
      if (reducedCongruence && reducedInterval.min >= 0) {
        const granger = this.reduceIntervalCongruence(reducedInterval, reducedCongruence);
        if (!granger) {
          return { ...state, sign: "BOTTOM", interval: undefined, congruence: undefined };
        }
        reducedInterval = granger.interval;
        reducedCongruence = granger.congruence;
      } else if (
        reducedInterval.min === reducedInterval.max &&
        Number.isFinite(reducedInterval.min) &&
        reducedInterval.min >= 0
      ) {
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

  constructor(wasmInstance?: WasmInstanceLike | null | any) {
    const resolved = wasmInstance === undefined ? getDefaultWasmInstance() : wasmInstance;
    if (resolved && typeof resolved === "object" && "exports" in resolved) {
      this.wasmModule = (resolved as WasmInstanceLike).exports;
    } else {
      this.wasmModule = resolved || null;
    }
  }

  /**
   * Returns true when the Rust/WASM evaluation engine (`lean_analyzer.wasm`) is active.
   */
  isUsingWasm(): boolean {
    return Boolean(
      this.wasmModule &&
      typeof this.wasmModule.lean_analyzer_version === "function"
    );
  }

  /**
   * Registers or updates an abstract lattice state for a named declaration/variable.
   */
  setDeclState(name: string, state: AbstractLatticeState): void {
    this.declarations.set(name, this.reduceState(state));
  }

  /**
   * Retrieves the abstract lattice state for a named declaration/variable.
   */
  getDeclState(name: string): AbstractLatticeState | undefined {
    return this.declarations.get(name);
  }

  /**
   * Initializes or attaches a WASM accelerated evaluation engine.
   * @param wasmBytes - Binary WASM buffer compiled from crates/lean-analyzer.
   */
  async loadWasmEngine(wasmBytes: Uint8Array): Promise<boolean> {
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
  reduceState(state: AbstractLatticeState): AbstractLatticeState {
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
  checkZoneSubDecreasing(guardDiff: number, step: number): "BOTTOM" | "FALSE" | "TRUE" | "TOP" {
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

  /**
   * Synthesizes a Lean 4 `termination_by` / `decreasing_by` clause when Zone DBM
   * proves `n - (i + step) < n - i` under guard `i - n <= guardDiff`.
   * Emits `by omega` by default and includes a custom domain tactic alternative
   * when custom project tactics are enabled or detected.
   */
  synthesizeTerminationDecreasingBy(
    guardDiff: number,
    step: number,
    options?: {
      measureExpr?: string;
      enableCustomProjectTactics?: boolean;
      customTacticName?: string;
      sourceContext?: string;
    }
  ): {
    verdict: "BOTTOM" | "FALSE" | "TRUE" | "TOP";
    decreasingBy: string | null;
    alternatives: string[];
    terminationSnippet: string | null;
  } {
    const verdict = this.checkZoneSubDecreasing(guardDiff, step);
    if (verdict !== "TRUE") {
      return {
        verdict,
        decreasingBy: null,
        alternatives: [],
        terminationSnippet: null
      };
    }
    const customTactic = options?.customTacticName || "scaled_omega";
    const customDetected = Boolean(
      options?.enableCustomProjectTactics ||
      Boolean(options?.customTacticName) ||
      (options?.sourceContext && /\b(?:scaled_omega|Scale100)\b/.test(options.sourceContext))
    );
    const decreasingBy = "by omega";
    const alternatives = customDetected ? ["by omega", `by ${customTactic}`] : ["by omega"];
    const measure = options?.measureExpr || "n - i";
    return {
      verdict,
      decreasingBy,
      alternatives,
      terminationSnippet: `termination_by ${measure}\ndecreasing_by omega`
    };
  }

  /**
   * Tightens two natural-number intervals `iv0 = [min0, max0]` and `iv1 = [min1, max1]`
   * under relational octagon constraints `sumLo <= x0 + x1 <= sumHi` and `x0 - x1 <= diffHi`
   * (`NatOctagonDomain`, Mine 2006 / Pelleau 2015).
   * Returns `[reducedIv0, reducedIv1]` or `null` if the system is unsatisfiable (`Bottom`).
   */
  reduceOctagonTwoVars(
    iv0: IntervalBound,
    iv1: IntervalBound,
    sumLo: number,
    sumHi: number,
    diffHi: number = Number.POSITIVE_INFINITY
  ): [IntervalBound, IntervalBound] | null {
    const MAX_I64 = 9223372036854775807n;
    const toI64 = (v: number): bigint =>
      !Number.isFinite(v) ? MAX_I64 : BigInt(Math.trunc(v));

    if (
      this.wasmModule &&
      typeof this.wasmModule.lean_analyzer_octagon_reduce_two_vars === "function" &&
      this.wasmModule.memory &&
      typeof this.wasmModule.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasmModule.lean_analyzer_get_scratch_ptr();
      const ok = this.wasmModule.lean_analyzer_octagon_reduce_two_vars(
        toI64(Math.max(0, iv0.min)),
        toI64(iv0.max),
        toI64(Math.max(0, iv1.min)),
        toI64(iv1.max),
        toI64(Math.max(0, sumLo)),
        toI64(sumHi),
        toI64(diffHi),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.wasmModule.memory.buffer, ptr, 4);
      const fromI64 = (b: bigint): number =>
        b >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(b);
      return [
        { min: fromI64(view[0]), max: fromI64(view[1]) },
        { min: fromI64(view[2]), max: fromI64(view[3]) }
      ];
    }

    // Pure-TS fallback: iterative interval-sum-diff propagation + integer halving
    let lo0 = Math.max(0, Math.trunc(iv0.min));
    let hi0 = Number.isFinite(iv0.max) ? Math.trunc(iv0.max) : Number.POSITIVE_INFINITY;
    let lo1 = Math.max(0, Math.trunc(iv1.min));
    let hi1 = Number.isFinite(iv1.max) ? Math.trunc(iv1.max) : Number.POSITIVE_INFINITY;
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
   * Tightens two natural-number intervals `iv0 = [xMin, xMax]` and `iv1 = [yMin, yMax]`
   * under a weighted linear / Karr affine conservation bound `sumMin <= a * x + b * y <= sumMax`
   * (`a > 0`, `b > 0`).
   * Returns `[reducedIv0, reducedIv1]` or `null` if the system is unsatisfiable (`Bottom`).
   */
  reduceWeightedLinearTwoVars(
    a: number,
    b: number,
    sumMin: number,
    sumMax: number,
    iv0: IntervalBound,
    iv1: IntervalBound
  ): [IntervalBound, IntervalBound] | null {
    const MAX_I64 = 9223372036854775807n;
    const toI64 = (v: number): bigint =>
      !Number.isFinite(v) ? MAX_I64 : BigInt(Math.trunc(v));

    const wasmFn =
      this.wasmModule
        ? this.wasmModule.lean_analyzer_weighted_linear_reduce ||
          this.wasmModule.lean_analyzer_WeightedSimplexReduce
        : null;
    if (
      typeof wasmFn === "function" &&
      this.wasmModule.memory &&
      typeof this.wasmModule.lean_analyzer_get_scratch_ptr === "function"
    ) {
      const ptr = this.wasmModule.lean_analyzer_get_scratch_ptr();
      const ok = wasmFn(
        toI64(a),
        toI64(b),
        toI64(Math.max(0, sumMin)),
        toI64(sumMax),
        toI64(Math.max(0, iv0.min)),
        toI64(iv0.max),
        toI64(Math.max(0, iv1.min)),
        toI64(iv1.max),
        ptr
      );
      if (ok === 0) return null;
      const view = new BigInt64Array(this.wasmModule.memory.buffer, ptr, 4);
      const fromI64 = (v: bigint): number =>
        v >= MAX_I64 ? Number.POSITIVE_INFINITY : Number(v);
      return [
        { min: fromI64(view[0]), max: fromI64(view[1]) },
        { min: fromI64(view[2]), max: fromI64(view[3]) }
      ];
    }

    const wa = Math.trunc(a);
    const wb = Math.trunc(b);
    if (wa <= 0 || wb <= 0) return null;
    let xLo = Math.max(0, Math.trunc(iv0.min));
    let xHi = Number.isFinite(iv0.max) ? Math.trunc(iv0.max) : Number.POSITIVE_INFINITY;
    let yLo = Math.max(0, Math.trunc(iv1.min));
    let yHi = Number.isFinite(iv1.max) ? Math.trunc(iv1.max) : Number.POSITIVE_INFINITY;
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
            const boundFromDivisor =
              r.max === Number.POSITIVE_INFINITY
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
            const maxRem =
              r.max === Number.POSITIVE_INFINITY
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
            interval = {
              min: Math.max(l.min, r.min),
              max: Number.isFinite(maxIn) ? mask - 1 : Number.POSITIVE_INFINITY
            };
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
            interval = {
              min: 0,
              max: Number.isFinite(maxIn) ? mask - 1 : Number.POSITIVE_INFINITY
            };
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
  evalExpr(expr: { op?: string; args?: any[]; value?: number }): AbstractLatticeState {
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
  evalCstNode(node: TreeSitterCstNode): AbstractLatticeState {
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

    // Identifier lookup in declaration state table
    if ((node.type === "identifier" || node.type === "ident") && node.text) {
      const decl = this.declarations.get(node.text);
      if (decl) {
        return this.reduceState(decl);
      }
    }

    // Parenthesized expression: ( e )
    if (
      (node.type === "paren_expression" || node.type === "parenthesized_expression") &&
      node.children &&
      node.children.length > 0
    ) {
      const inner = node.children.find((c) => c.type !== "(" && c.type !== ")");
      if (inner) {
        return this.evalCstNode(inner);
      }
    }

    // Application node: flat (f arg1 arg2), unary (Nat.succ arg1), or curried ((f arg1) arg2)
    if (node.type === "apply_expression" && node.children) {
      if (node.children.length >= 3) {
        const fnNode = node.children[0];
        const fnName = fnNode.text || "";
        const left = this.evalCstNode(node.children[1]);
        const right = this.evalCstNode(node.children[2]);
        const res = this.evalBinaryNatOp(fnName, left, right);
        if (res !== null) {
          return res;
        }
      } else if (node.children.length === 2) {
        const fnNode = node.children[0];
        if (fnNode.type === "apply_expression" && fnNode.children && fnNode.children.length === 2) {
          const opName = fnNode.children[0].text || "";
          const left = this.evalCstNode(fnNode.children[1]);
          const right = this.evalCstNode(node.children[1]);
          const res = this.evalBinaryNatOp(opName, left, right);
          if (res !== null) {
            return res;
          }
        }
        const unaryName = fnNode.text || "";
        if (unaryName === "Nat.succ") {
          const arg = this.evalCstNode(node.children[1]);
          const res = this.evalBinaryNatOp("Nat.add", arg, this.evalExpr({ value: 1 }));
          if (res !== null) return res;
        } else if (unaryName === "Nat.pred") {
          const arg = this.evalCstNode(node.children[1]);
          const res = this.evalBinaryNatOp("Nat.sub", arg, this.evalExpr({ value: 1 }));
          if (res !== null) return res;
        }
      }
    }

    // Binary infix expression: (left op right)
    if (
      (node.type === "binary_expression" || node.type === "infix_expression") &&
      node.children &&
      node.children.length >= 3
    ) {
      const left = this.evalCstNode(node.children[0]);
      const opName = node.children[1].text || node.children[1].type || "";
      const right = this.evalCstNode(node.children[2]);
      const res = this.evalBinaryNatOp(opName, left, right);
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
  widen(
    prevRaw: AbstractLatticeState,
    nextRaw: AbstractLatticeState,
    thresholds?: number[]
  ): AbstractLatticeState {
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
        ? thresholds && thresholds.length > 0
          ? AbstractLattice.widenIntervalWithThresholds(prev.interval, next.interval, thresholds, isNat)
          : AbstractLattice.widenInterval(prev.interval, next.interval, isNat)
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
  narrow(wideRaw: AbstractLatticeState, refinedRaw: AbstractLatticeState): AbstractLatticeState {
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
  computeFixpoint(
    init: AbstractLatticeState,
    transferFn: (curr: AbstractLatticeState) => AbstractLatticeState,
    maxIterations: number = 20
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
  computeWideningFixpoint(
    init: AbstractLatticeState,
    transferFn: (curr: AbstractLatticeState) => AbstractLatticeState,
    maxIterations: number = 20,
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
  diagnoseExpr(expr: { op?: string; args?: any[]; value?: number }): {
    state: AbstractLatticeState;
    certificates: DiagnosticCertificate[];
  } {
    const certificates: DiagnosticCertificate[] = [];

    const visit = (node: { op?: string; args?: any[]; value?: number }) => {
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

  /**
   * Scans Lean 4 source text for literal natural-number arithmetic hazards
   * (Nat subtraction truncation `a - b` where `a <= b` and `b > 0`, and
   * division/modulo by literal zero `a / 0` or `a % 0`), returning line-indexed
   * `DiagnosticCertificate` entries without spawning `lake serve`.
   */
  scanSourceForNatCertificates(sourceText: string): Array<
    DiagnosticCertificate & { line: number; col: number }
  > {
    const out: Array<DiagnosticCertificate & { line: number; col: number }> = [];
    const lines = sourceText.split(/\r?\n/);
    let inBlockComment = 0;

    for (let idx = 0; idx < lines.length; idx++) {
      const rawLine = lines[idx];
      let clean = "";
      let i = 0;
      while (i < rawLine.length) {
        if (inBlockComment > 0) {
          if (rawLine[i] === "/" && rawLine[i + 1] === "-") {
            inBlockComment++;
            clean += "  ";
            i += 2;
          } else if (rawLine[i] === "-" && rawLine[i + 1] === "/") {
            inBlockComment--;
            clean += "  ";
            i += 2;
          } else {
            clean += " ";
            i++;
          }
        } else {
          if (rawLine[i] === "-" && rawLine[i + 1] === "-") {
            clean += " ".repeat(rawLine.length - i);
            break;
          } else if (rawLine[i] === "/" && rawLine[i + 1] === "-") {
            inBlockComment++;
            clean += "  ";
            i += 2;
          } else {
            clean += rawLine[i];
            i++;
          }
        }
      }

      // 1. Explicit Nat.sub / Nat.div / Nat.mod on literal naturals
      const prefixRe = /\b(Nat\.sub|Nat\.div|Nat\.mod)\s+(\d+)\s+(\d+)\b/g;
      for (const m of clean.matchAll(prefixRe)) {
        const op = m[1];
        const a = Number.parseInt(m[2], 10);
        const b = Number.parseInt(m[3], 10);
        if (Number.isFinite(a) && Number.isFinite(b)) {
          const diag = this.diagnoseExpr({ op, args: [{ value: a }, { value: b }] });
          for (const cert of diag.certificates) {
            out.push({
              ...cert,
              line: idx + 1,
              col: (m.index ?? 0) + 1
            });
          }
        }
      }

      // 2. Infix division / modulo by literal zero: `a / 0` or `a % 0`
      const divZeroRe = /\b(\d+)\s*(\/|%)\s*(0)\b/g;
      for (const m of clean.matchAll(divZeroRe)) {
        const a = Number.parseInt(m[1], 10);
        const op = m[2];
        if (Number.isFinite(a)) {
          const diag = this.diagnoseExpr({ op, args: [{ value: a }, { value: 0 }] });
          for (const cert of diag.certificates) {
            out.push({
              ...cert,
              line: idx + 1,
              col: (m.index ?? 0) + 1
            });
          }
        }
      }
    }

    return out;
  }

  /**
   * Wave 8 Galois-Guided Counterexample Search Pruning (`PELLEAU2015 s2.2 p1`, `SIMONVRA s8.2 p1`):
   * Extracts natural-number variable domains `[min, max]`, congruence strides `n % s = o`,
   * and two-variable octagonal sum constraints `x + y <= c` / `x + y = c` from a Lean theorem header,
   * applies mutual Granger + Octagon domain reduction, and returns a tightened `recommendedMaxSize`
   * (or `isVacuous: true` when the hypotheses have empty intersection `Bottom`).
   */
  analyzeHeaderHypothesisDomains(header: string): {
    domains: Record<string, { interval: IntervalBound; congruence?: NatCongruence }>;
    isVacuous: boolean;
    recommendedMaxSize: number | null;
  } {
    const vars = new Map<string, { interval: IntervalBound; congruence?: NatCongruence }>();

    // 1. Collect explicit `(x y : Nat)` or `(x : Nat)` binders (plus implicit mentions in hypotheses)
    const binderRe = /\(\s*([A-Za-z_][A-Za-z0-9_'\s]*)\s*:\s*(?:Nat|\u2115)\s*\)/g;
    for (const m of header.matchAll(binderRe)) {
      const names = m[1].trim().split(/\s+/);
      for (const name of names) {
        if (name) {
          vars.set(name, { interval: { min: 0, max: Number.POSITIVE_INFINITY } });
        }
      }
    }

    const ensureVar = (name: string) => {
      if (!vars.has(name)) {
        vars.set(name, { interval: { min: 0, max: Number.POSITIVE_INFINITY } });
      }
      return vars.get(name)!;
    };

    // Strip the final goal conclusion after the last `:` or `->` / `\u2192` when possible so we only
    // harvest antecedent/hypothesis constraints (or binder hypotheses `(h : ...)`).
    const hypChunks: string[] = [];
    const parenGroupRe = /\([^()]+\)/g;
    for (const m of header.matchAll(parenGroupRe)) {
      hypChunks.push(m[0]);
    }
    const turnstileParts = header.split(/\|-|\u22A2/);
    if (turnstileParts.length > 1) {
      hypChunks.push(turnstileParts[0]);
    }
    const arrowParts = header.split(/->|\u2192/);
    if (arrowParts.length > 1) {
      for (let i = 0; i < arrowParts.length - 1; i++) {
        hypChunks.push(arrowParts[i]);
      }
    }
    const hypText = hypChunks.join(" ; ");

    // 2. Unary upper bounds: `x <= C`, `x < C`, `x = C`
    const upperRe = /\b([A-Za-z_][A-Za-z0-9_']*)\s*(<=|\u2264|<|={1,2})\s*(\d+)\b/g;
    for (const m of hypText.matchAll(upperRe)) {
      const v = m[1];
      const op = m[2];
      const c = Number.parseInt(m[3], 10);
      if (Number.isFinite(c)) {
        const entry = ensureVar(v);
        if (op === "=" || op === "==") {
          entry.interval.min = Math.max(entry.interval.min, c);
          entry.interval.max = Math.min(entry.interval.max, c);
        } else {
          const cap = op === "<" ? c - 1 : c;
          entry.interval.max = Math.min(entry.interval.max, cap);
        }
      }
    }

    // 3. Unary lower bounds: `C <= x`, `C < x`, `x >= C`, `x > C`
    const lowerLeftRe = /\b(\d+)\s*(<=|\u2264|<)\s*([A-Za-z_][A-Za-z0-9_']*)\b/g;
    for (const m of hypText.matchAll(lowerLeftRe)) {
      const c = Number.parseInt(m[1], 10);
      const op = m[2];
      const v = m[3];
      if (Number.isFinite(c)) {
        const entry = ensureVar(v);
        const floor = op === "<" ? c + 1 : c;
        entry.interval.min = Math.max(entry.interval.min, floor);
      }
    }
    const lowerRightRe = /\b([A-Za-z_][A-Za-z0-9_']*)\s*(>=|\u2265|>)\s*(\d+)\b/g;
    for (const m of hypText.matchAll(lowerRightRe)) {
      const v = m[1];
      const op = m[2];
      const c = Number.parseInt(m[3], 10);
      if (Number.isFinite(c)) {
        const entry = ensureVar(v);
        const floor = op === ">" ? c + 1 : c;
        entry.interval.min = Math.max(entry.interval.min, floor);
      }
    }

    // 4. Congruence hypotheses: `x % S = O` or `x % S == O`
    const congRe = /\b([A-Za-z_][A-Za-z0-9_']*)\s*%\s*(\d+)\s*={1,2}\s*(\d+)\b/g;
    for (const m of hypText.matchAll(congRe)) {
      const v = m[1];
      const s = Number.parseInt(m[2], 10);
      const o = Number.parseInt(m[3], 10);
      if (Number.isFinite(s) && Number.isFinite(o) && s > 0) {
        if (o >= s) {
          return { domains: {}, isVacuous: true, recommendedMaxSize: null };
        }
        const entry = ensureVar(v);
        entry.congruence = { stride: s, offset: o };
      }
    }

    // 5. Apply Granger interval-congruence reduction per variable
    for (const [v, entry] of vars.entries()) {
      if (entry.interval.min > entry.interval.max || entry.interval.max < 0) {
        return { domains: {}, isVacuous: true, recommendedMaxSize: null };
      }
      if (entry.congruence) {
        const reduced = AbstractLattice.reduceIntervalCongruence(entry.interval, entry.congruence);
        if (!reduced) {
          return { domains: {}, isVacuous: true, recommendedMaxSize: null };
        }
        entry.interval = reduced.interval;
        entry.congruence = reduced.congruence;
        vars.set(v, entry);
      }
    }

    // 6. Octagonal two-variable sum constraints: `x + y <= C`, `x + y < C`, `x + y = C`
    const sumRe =
      /(?:^|[^*\w])([A-Za-z_][A-Za-z0-9_']*)\s*\+\s*([A-Za-z_][A-Za-z0-9_']*)\s*(<=|\u2264|<|={1,2})\s*(\d+)\b/g;
    for (const m of hypText.matchAll(sumRe)) {
      const v0 = m[1];
      const v1 = m[2];
      const op = m[3];
      const c = Number.parseInt(m[4], 10);
      if (v0 !== v1 && Number.isFinite(c)) {
        const e0 = ensureVar(v0);
        const e1 = ensureVar(v1);
        const sumLo = op === "=" || op === "==" ? c : 0;
        const sumHi = op === "<" ? c - 1 : c;
        if (sumHi < 0) {
          return { domains: {}, isVacuous: true, recommendedMaxSize: null };
        }
        const oct = this.reduceOctagonTwoVars(e0.interval, e1.interval, sumLo, sumHi);
        if (!oct) {
          return { domains: {}, isVacuous: true, recommendedMaxSize: null };
        }
        e0.interval = oct[0];
        e1.interval = oct[1];
      }
    }

    // 7. Weighted two-variable linear / Karr affine constraints: `a * x + b * y <= C`, `< C`, `= C`, `>= C`
    const weightedSumRe =
      /(?:(\d+)\s*\*\s*)?([A-Za-z_][A-Za-z0-9_']*)\s*\+\s*(?:(\d+)\s*\*\s*)?([A-Za-z_][A-Za-z0-9_']*)\s*(<=|\u2264|<|={1,2}|>=|\u2265|>)\s*(\d+)\b/g;
    for (const m of hypText.matchAll(weightedSumRe)) {
      const w0 = m[1] !== undefined ? Number.parseInt(m[1], 10) : 1;
      const v0 = m[2];
      const w1 = m[3] !== undefined ? Number.parseInt(m[3], 10) : 1;
      const v1 = m[4];
      const op = m[5];
      const c = Number.parseInt(m[6], 10);
      if (
        v0 !== v1 &&
        Number.isFinite(w0) &&
        Number.isFinite(w1) &&
        w0 > 0 &&
        w1 > 0 &&
        Number.isFinite(c) &&
        (m[1] !== undefined || m[3] !== undefined || op === ">=" || op === "\u2265" || op === ">")
      ) {
        const e0 = ensureVar(v0);
        const e1 = ensureVar(v1);
        let sumLo = 0;
        let sumHi = Number.POSITIVE_INFINITY;
        if (op === "=" || op === "==") {
          sumLo = c;
          sumHi = c;
        } else if (op === "<") {
          sumHi = c - 1;
        } else if (op === "<=" || op === "\u2264") {
          sumHi = c;
        } else if (op === ">=" || op === "\u2265") {
          sumLo = c;
        } else if (op === ">") {
          sumLo = c + 1;
        }
        if (sumHi < 0) {
          return { domains: {}, isVacuous: true, recommendedMaxSize: null };
        }
        const reduced = this.reduceWeightedLinearTwoVars(
          w0,
          w1,
          sumLo,
          sumHi,
          e0.interval,
          e1.interval
        );
        if (!reduced) {
          return { domains: {}, isVacuous: true, recommendedMaxSize: null };
        }
        e0.interval = reduced[0];
        e1.interval = reduced[1];
      }
    }

    const domains: Record<string, { interval: IntervalBound; congruence?: NatCongruence }> = {};
    let maxFiniteUpper = 0;
    let hasTightenedBound = false;
    for (const [k, v] of vars.entries()) {
      if (v.interval.min > v.interval.max) {
        return { domains: {}, isVacuous: true, recommendedMaxSize: null };
      }
      domains[k] = v;
      if (Number.isFinite(v.interval.max)) {
        hasTightenedBound = true;
        if (v.interval.max > maxFiniteUpper) {
          maxFiniteUpper = v.interval.max;
        }
      }
    }

    const recommendedMaxSize = hasTightenedBound
      ? Math.max(1, Math.min(5000, maxFiniteUpper + 1))
      : null;

    return {
      domains,
      isVacuous: false,
      recommendedMaxSize
    };
  }

  /**
   * Evaluates a Lean 4 goal and optional proof script using the hybrid
   * `lean-analyzer` + AltProof route/tactic/legibility/cost pipeline
   * (`SPEC-ALT-PROOF-DES`, `ALT_PROOF_SAIR_BRIDGE`).
   */
  analyzeAltProof(goalText: string, proofText: string = ""): AltProofAnalysisReport {
    return analyzeAltProofGoalAndBlock(this, goalText, proofText);
  }
}

export interface AltProofRoute {
  id: string;
  family: string;
  matchShape: string;
  rewriteHint: string;
  costHint: string;
  provenance: string;
}

export interface AltProofGoalFeatures {
  hasFinsetSum: boolean;
  hasFinsetNonneg: boolean;
  hasFinsetMono: boolean;
  hasAbs: boolean;
  hasIteOrDecide: boolean;
  hasNegOrContra: boolean;
  hasNatArith: boolean;
  hasWellFounded: boolean;
  hasWellFormed: boolean;
  hasChannelOrPrior: boolean;
}

export interface AltProofTacticRecommendation {
  tactic: string;
  targetPattern: string;
  rationale: string;
  estimatedHeartbeats: number;
  confidence: number;
  projectedCostX10: number;
}

export interface AltProofLegibilityScore {
  steps: number;
  renderable: number;
  verboseScore: number;
  heavySteps: string[];
}

export interface AltProofAbstractCertification {
  certified: boolean;
  isVacuous: boolean;
  targetVerified: boolean;
  domains: Record<string, { interval: IntervalBound; congruence?: NatCongruence }>;
  targetSummary?: string;
  natSubTruncationWarning?: string;
}

export interface AltProofAnalysisReport {
  goal: string;
  features: AltProofGoalFeatures;
  relevantRoutes: AltProofRoute[];
  recommendations: AltProofTacticRecommendation[];
  legibility: AltProofLegibilityScore;
  baselineCostX10: number;
  bestTactic: string | null;
  bestEstimatedHeartbeats: number;
  staticCertificates: Array<DiagnosticCertificate & { line: number; col: number }>;
  zoneDecreasingHint?: string;
  abstractCertification?: AltProofAbstractCertification;
}

export const ALTPROOF_ROUTE_TABLE: AltProofRoute[] = [
  {
    id: "extract-shared-block",
    family: "extraction",
    matchShape: "a >=3-line proof block reused verbatim or modulo renaming",
    rewriteHint: "name the block as a lemma; call it at each site",
    costHint: "high-yield: counts once, serves N sites",
    provenance: "long-proof campaign fixtures 1-15, 17 (36 shared lemmas)"
  },
  {
    id: "extract-mathlib-absent",
    family: "extraction",
    matchShape: "a generic block with no Mathlib equivalent (verified absent before naming)",
    rewriteHint: "name it in the owning module; flag as an upstreaming candidate",
    costHint: "highest yield: reusable beyond the corpus",
    provenance: "fixtures 10-11 (cesaro_tendsto_of_geometric_bound -> PR #44591; sum_mul_le_sum_mul_sum)"
  },
  {
    id: "extract-horizon-package",
    family: "extraction",
    matchShape: "three or more inline steps serving one standing theorem family",
    rewriteHint: "package the steps as a named lemma trio in the theorem's module",
    costHint: "high-yield: the Doeblin package pattern",
    provenance: "fixture 12 (doeblin_card_mul_le_one, realStep_iterate_mul, stationary_ge_of_doeblin)"
  },
  {
    id: "extract-cauchy-toolkit",
    family: "extraction",
    matchShape: "a Cauchy/convergence argument assembled from pointwise and sum-level lemmas",
    rewriteHint: "extract the four standard sub-steps as reusable convergence lemmas",
    costHint: "high-yield: the GAP-7 pattern (154 -> ~40)",
    provenance: "fixture 17 (iterate_sum_cauchy, pointwise_cauchy_of_sum_cauchy, sum_dist_tendsto_of_pointwise, step_fixedpoint_of_sum_dist_tendsto)"
  },
  {
    id: "uniform-simp-collapse",
    family: "reflection",
    matchShape: "branched case analysis where one uniform simp set closes every branch",
    rewriteHint: "replace the branches with one uniform simp call (the boolean-reflection pattern)",
    costHint: "high-yield: 76 lines/6 branches -> cleared (fixture 16)",
    provenance: "fixture 16 (gate_row_diff_bound)"
  },
  {
    id: "redirect-by-contradiction",
    family: "redirect",
    matchShape: "by_contra-heavy proofs with a constructible direct witness",
    rewriteHint: "restate as a direct construction (the JAR 2016 redirect class)",
    costHint: "reserved: no corpus fixture yet - the tool's first hit becomes it",
    provenance: "JAR16 redirect procedure; ballot B3"
  },
  {
    id: "algorithm-class-substitution",
    family: "algorithm-class-substitution",
    matchShape: "exponential or unhoisted recursion with an equivalent closed-form or DP reduction",
    rewriteHint: "substitute algorithm class (e.g. in-place DP or structural sieve) and prove equivalence to spec",
    costHint: "highest kernel yield: 20-30x reduction in kernel steps / rfl time",
    provenance: "SAIR Lean Kernel Challenge lanes (partition in-place DP S1/S1b, primecount sieve S6)"
  },
  {
    id: "kernel-friendly-term-design",
    family: "kernel-friendly-term-design",
    matchShape: "structural recursion or helper calls with heavy defeq unfolding overhead",
    rewriteHint: "refactor to kernel-friendly primitives (structural Nat.rec, unrolled trial division, import-minimal path)",
    costHint: "high kernel yield: reduces defeq heartbeats and avoids WellFounded.fix traps",
    provenance: "SAIR Lean Kernel Challenge lanes (primecount L1 structural trial division S5)"
  }
];

export function computeAltProofCostX10(
  lines: number,
  sharedLemmas: number = 0,
  upstream: boolean = false,
  kernelCostUnits: number = 0
): number {
  const base = Math.max(0, Math.trunc(lines)) * 1;
  const bonus = Math.max(0, Math.trunc(sharedLemmas)) * 50;
  const up = upstream ? 200 : 0;
  const kCost = Math.max(0, Math.trunc(kernelCostUnits)) * 10;
  return base - bonus - up + kCost;
}

const ALTPROOF_RENDERABLE_PATTERNS: RegExp[] = [
  /^exact\s+\S/,
  /^apply\s+\S/,
  /^have\s+\w+\s*:?=?\s*\S+/,
  /^(unfold|simp|simp_rw|rw|erw)\b/,
  /^(linarith|nlinarith|omega|ring|ring_nf|field_simp|positivity|norm_num|rfl|exact\?|aesop|grind|decide|sum_congr_ring|finset_nonneg|finset_mono|wellformed_tac|channel_fields|alt_proof|elegance\?)\b/,
  /^(constructor|refine|use|exists|intro|intros|induction|cases|rcases|obtain|fin_cases)\b/
];

export function scoreAltProofLegibility(proofText: string): AltProofLegibilityScore {
  const steps = (proofText || "")
    .split(/\r?\n/)
    .map((ln) => ln.trim())
    .filter((ln) => ln.length > 0 && !ln.startsWith("--"));
  let renderable = 0;
  const heavySteps: string[] = [];
  for (const st of steps) {
    const ok = ALTPROOF_RENDERABLE_PATTERNS.some((p) => p.test(st));
    if (ok) {
      renderable++;
    } else if (heavySteps.length < 5) {
      heavySteps.push(st.slice(0, 80));
    }
  }
  const total = steps.length;
  return {
    steps: total,
    renderable,
    verboseScore: total > 0 ? Number((renderable / total).toFixed(4)) : 1.0,
    heavySteps
  };
}

function extractGoalTarget(goalText: string): string {
  let raw = (goalText || "").trim();
  if (raw.startsWith("```")) {
    raw = raw.replace(/^```[a-zA-Z0-9_-]*\s*/, "").replace(/\s*```$/, "");
  }
  const parts = raw.split(/(?:\|-|\u22A2)/);
  if (parts.length > 1) {
    return parts[parts.length - 1].trim();
  }
  const arrowParts = raw.split(/->|\u2192/);
  if (arrowParts.length > 1) {
    return arrowParts[arrowParts.length - 1].trim();
  }
  return raw;
}

function evalLinearExprInterval(
  expr: string,
  domains: Record<string, { interval: IntervalBound; congruence?: NatCongruence }>
): { interval: IntervalBound; natSubWarning?: string } | null {
  const s = expr.trim();
  if (/^\d+$/.test(s)) {
    const v = Number.parseInt(s, 10);
    return { interval: { min: v, max: v } };
  }
  if (/^[A-Za-z_][A-Za-z0-9_']*$/.test(s)) {
    const d = domains[s];
    return d ? { interval: { ...d.interval } } : null;
  }
  const mulMatch = s.match(/^(\d+)\s*\*\s*([A-Za-z_][A-Za-z0-9_']*)$/);
  if (mulMatch) {
    const k = Number.parseInt(mulMatch[1], 10);
    const d = domains[mulMatch[2]];
    if (!d) return null;
    return {
      interval: {
        min: k * d.interval.min,
        max: Number.isFinite(d.interval.max) ? k * d.interval.max : Number.POSITIVE_INFINITY
      }
    };
  }
  const addMatch = s.match(
    /^(?:(\d+)\s*\*\s*)?([A-Za-z_][A-Za-z0-9_']*)\s*\+\s*(?:(\d+)\s*\*\s*)?([A-Za-z_][A-Za-z0-9_']*|\d+)$/
  );
  if (addMatch) {
    const w0 = addMatch[1] !== undefined ? Number.parseInt(addMatch[1], 10) : 1;
    const d0 = domains[addMatch[2]];
    if (!d0) return null;
    const leftMin = w0 * d0.interval.min;
    const leftMax = Number.isFinite(d0.interval.max) ? w0 * d0.interval.max : Number.POSITIVE_INFINITY;
    const rhsToken = addMatch[4];
    if (/^\d+$/.test(rhsToken)) {
      const c = Number.parseInt(rhsToken, 10);
      return { interval: { min: leftMin + c, max: leftMax + c } };
    }
    const w1 = addMatch[3] !== undefined ? Number.parseInt(addMatch[3], 10) : 1;
    const d1 = domains[rhsToken];
    if (!d1) return null;
    const rightMin = w1 * d1.interval.min;
    const rightMax = Number.isFinite(d1.interval.max) ? w1 * d1.interval.max : Number.POSITIVE_INFINITY;
    return { interval: { min: leftMin + rightMin, max: leftMax + rightMax } };
  }
  const subMatch = s.match(/^([A-Za-z_][A-Za-z0-9_']*|\d+)\s*-\s*([A-Za-z_][A-Za-z0-9_']*|\d+)$/);
  if (subMatch) {
    const l = evalLinearExprInterval(subMatch[1], domains);
    const r = evalLinearExprInterval(subMatch[2], domains);
    if (!l || !r) return null;
    const min = Math.max(0, l.interval.min - r.interval.max);
    const max = Math.max(0, l.interval.max - r.interval.min);
    let natSubWarning: string | undefined;
    if (l.interval.max <= r.interval.min && r.interval.min > 0) {
      natSubWarning = `Natural subtraction \`${s}\` on [${l.interval.min}, ${l.interval.max}] - [${r.interval.min}, ${r.interval.max}] saturates to [0, 0] (NatSubTruncation).`;
    } else if (l.interval.min < r.interval.max && r.interval.max > 0) {
      natSubWarning = `Natural subtraction \`${s}\` on [${l.interval.min}, ${l.interval.max}] - [${r.interval.min}, ${r.interval.max}] can underflow and truncate at 0; add guard \`${subMatch[2]} <= ${subMatch[1]}\`.`;
    }
    return { interval: { min, max }, natSubWarning };
  }
  return null;
}

export function computeAltProofAbstractCertification(
  interpreter: LeanAbstractInterpreter,
  goalText: string,
  target: string
): AltProofAbstractCertification | undefined {
  const domRes = interpreter.analyzeHeaderHypothesisDomains(goalText);
  const hasDomains = Object.keys(domRes.domains).length > 0;
  let targetVerified = false;
  let targetSummary: string | undefined;
  let natSubTruncationWarning: string | undefined;

  if (domRes.isVacuous) {
    return {
      certified: true,
      isVacuous: true,
      targetVerified: true,
      domains: domRes.domains,
      targetSummary: "Hypotheses reduce to Bottom (unreachable / vacuous branch); discharge via omega."
    };
  }

  const relMatch = target.match(/^(.+?)\s*(<=|\u2264|<|>=|\u2265|>|={1,2})\s*(.+)$/);
  if (relMatch && hasDomains) {
    const lhsExpr = relMatch[1].trim();
    const op = relMatch[2];
    const rhsExpr = relMatch[3].trim();
    const lhsEval = evalLinearExprInterval(lhsExpr, domRes.domains);
    const rhsEval = evalLinearExprInterval(rhsExpr, domRes.domains);
    if (lhsEval?.natSubWarning) {
      natSubTruncationWarning = lhsEval.natSubWarning;
    } else if (rhsEval?.natSubWarning) {
      natSubTruncationWarning = rhsEval.natSubWarning;
    }
    if (lhsEval && rhsEval) {
      const l = lhsEval.interval;
      const r = rhsEval.interval;
      if (op === "<=" || op === "\u2264") {
        targetVerified = l.max <= r.min;
      } else if (op === "<") {
        targetVerified = l.max < r.min;
      } else if (op === ">=" || op === "\u2265") {
        targetVerified = l.min >= r.max;
      } else if (op === ">") {
        targetVerified = l.min > r.max;
      } else if (op === "=" || op === "==") {
        targetVerified = l.min === l.max && r.min === r.max && l.min === r.min;
      }
      if (targetVerified) {
        targetSummary = `Certified \`${target}\` via abstract domain reduction (\`${lhsExpr}\` in [${l.min}, ${l.max}], \`${rhsExpr}\` in [${r.min}, ${r.max}]).`;
      }
    }
  }

  if (!hasDomains && !targetVerified && !natSubTruncationWarning) {
    return undefined;
  }

  return {
    certified: targetVerified || domRes.isVacuous,
    isVacuous: domRes.isVacuous,
    targetVerified,
    domains: domRes.domains,
    targetSummary,
    natSubTruncationWarning
  };
}

export function analyzeAltProofGoalAndBlock(
  interpreter: LeanAbstractInterpreter,
  goalText: string,
  proofText: string = ""
): AltProofAnalysisReport {
  const goal = goalText || "";
  const target = extractGoalTarget(goal);
  const proof = proofText || "";
  const combined = `${goal}\n${proof}`;
  const targetNoArrows = target.replace(/->/g, " ").replace(/=>/g, " ");

  const hasFinsetSum = /(?:\bFinset\.sum\b|\u2211|\bsum_sub_distrib\b|\bsum_add_distrib\b|\bmul_sum\b|\bsum_mul\b)/.test(combined);
  const hasFinsetSumInTargetOrProof = /(?:\bFinset\.sum\b|\u2211|\bsum_sub_distrib\b|\bsum_add_distrib\b|\bmul_sum\b|\bsum_mul\b)/.test(`${target}\n${proof}`);
  const hasFinsetNonneg =
    /(?:0\s*(?:<=|\u2264)\s*(?:Finset\.sum\b|\u2211))/.test(target) ||
    /\b(?:Finset\.sum_nonneg|finset_nonneg)\b/.test(proof);
  const hasFinsetMono =
    /(?:(?:Finset\.sum\b|\u2211)[\s\S]*?(?:<=|\u2264)[\s\S]*?(?:Finset\.sum\b|\u2211))/.test(target) ||
    /\b(?:Finset\.sum_le_sum|finset_mono)\b/.test(proof);
  const hasAbs = /(?:\babs\b|\bNorm\.norm\b|\bDist\.dist\b|\|[^|]+\|)/.test(combined);
  const hasIteOrDecide = /(?:\bite\b|\bdite\b|\bdecide\b|\bif\b[\s\S]+?\bthen\b|\bFin\s+\d+|\btrue\b|\bfalse\b)/.test(combined);
  const hasNegOrContra = /(?:\bNot\b|\bFalse\b|\bby_contra\b|\u00AC)/.test(combined);
  const hasNatContext = /(?:\bNat\b|\bInt\b|\bdiv\b|\bmod\b|\u2115|\u2124)/.test(goal) ||
    /\b\d+\s*(?:\+|-|\*|<=|<|>=|>)\s*\d+\b/.test(targetNoArrows);
  const hasArithOp = /(?:\+|-|\*|<=|<|>=|>|\u2264|\u2265)/.test(targetNoArrows);
  const hasRealLin = /(?:\bReal\b|\u211d|\blinarith\b)/.test(combined);
  const hasWellFounded = /(?:\bWellFounded\.fix\b|\btermination_by\b|\bdecreasing_by\b)/.test(combined);
  const hasWellFormed = /(?:\bWellFormed\b|\bwellformed_tac\b|\bfin_cases\b[\s\S]*?\bnorm_num\b)/.test(`${target}\n${proof}`);
  const hasChannelOrPrior = /(?:\bChannel\b|\bPrior\b|\bchannel_fields\b)/.test(`${target}\n${proof}`);
  const hasNatArith = Boolean(
    (hasNatContext || (hasArithOp && !hasFinsetSumInTargetOrProof && !hasWellFormed)) &&
    hasArithOp &&
    !hasRealLin &&
    !hasFinsetSumInTargetOrProof
  );

  const features: AltProofGoalFeatures = {
    hasFinsetSum,
    hasFinsetNonneg,
    hasFinsetMono,
    hasAbs,
    hasIteOrDecide,
    hasNegOrContra,
    hasNatArith,
    hasWellFounded,
    hasWellFormed,
    hasChannelOrPrior
  };

  const pickedRoutes = ALTPROOF_ROUTE_TABLE.filter((r) => {
    switch (r.id) {
      case "extract-shared-block":
      case "extract-mathlib-absent":
        return features.hasFinsetSum || features.hasAbs;
      case "extract-horizon-package":
        return features.hasFinsetSum && features.hasAbs;
      case "extract-cauchy-toolkit":
        return features.hasAbs;
      case "uniform-simp-collapse":
        return features.hasIteOrDecide || features.hasNatArith;
      case "redirect-by-contradiction":
        return features.hasNegOrContra;
      case "algorithm-class-substitution":
        return features.hasFinsetSum || features.hasWellFounded;
      case "kernel-friendly-term-design":
        return features.hasWellFounded || features.hasNatArith;
      default:
        return false;
    }
  });
  const relevantRoutes = pickedRoutes.length > 0 ? pickedRoutes : ALTPROOF_ROUTE_TABLE.slice(0, 3);

  const abstractCertification = computeAltProofAbstractCertification(interpreter, goal, target);
  const staticCertificates = interpreter.scanSourceForNatCertificates(combined);
  if (abstractCertification?.natSubTruncationWarning) {
    staticCertificates.push({
      kind: "NatSubTruncation",
      operator: "Nat.sub",
      summary: abstractCertification.natSubTruncationWarning,
      hint: "Add guard `b <= a` or switch to `Int` subtraction before invoking `omega`.",
      line: 1,
      col: 1
    });
  }

  const recommendations: AltProofTacticRecommendation[] = [];
  const pushRec = (
    tactic: string,
    targetPattern: string,
    rationale: string,
    estimatedHeartbeats: number,
    confidence: number
  ) => {
    const kUnits = Math.floor(estimatedHeartbeats / 1000);
    recommendations.push({
      tactic,
      targetPattern,
      rationale,
      estimatedHeartbeats,
      confidence,
      projectedCostX10: computeAltProofCostX10(1, 0, false, kUnits)
    });
  };

  if (hasNatArith || abstractCertification?.certified) {
    const certBoost = abstractCertification?.certified ? 0.07 : 0;
    const certNote = abstractCertification?.targetSummary
      ? ` (${abstractCertification.targetSummary})`
      : "";
    pushRec(
      "omega",
      "linear-nat-int-arithmetic",
      `Native Lean 4 Presburger arithmetic decision procedure; eliminates manual induction on inequalities.${certNote}`,
      abstractCertification?.certified ? 120 : 150,
      Math.min(0.99, Number((0.92 + certBoost).toFixed(2)))
    );
  }
  if (hasRealLin) {
    pushRec(
      "linarith",
      "linear-real-inequalities",
      "Fourier-Motzkin elimination over real linear combinations.",
      350,
      0.88
    );
  }
  if (hasFinsetSumInTargetOrProof) {
    pushRec(
      "sum_congr_ring",
      "finset-sum-linearity-pointwise-ring",
      "Normalizes Finset.sum linearity (sum_add_distrib, sum_sub_distrib, mul_sum, sum_mul) and closes pointwise ring equalities via Finset.sum_congr.",
      260,
      0.91
    );
  }
  if (hasFinsetNonneg) {
    pushRec(
      "finset_nonneg",
      "finset-sum-nonneg-positivity",
      "Discharges 0 <= sum_i f i via Finset.sum_nonneg, pointwise hypothesis instantiation, and positivity/linarith/nlinarith/omega.",
      240,
      0.90
    );
  }
  if (hasFinsetMono) {
    pushRec(
      "finset_mono",
      "finset-sum-pointwise-monotonicity",
      "Discharges sum_i f i <= sum_i g i via Finset.sum_le_sum, pointwise hypothesis instantiation, and ordered-ring monotonicity closers.",
      250,
      0.91
    );
  }
  if (hasWellFormed) {
    const wfBoost = abstractCertification?.certified ? 0.05 : 0;
    pushRec(
      "wellformed_tac",
      "finite-simplex-wellformed-conjunction",
      "Discharges five-field WellFormed conjunctions over Fin 1..8 via fin_cases and Fin.sum_univ_one..eight + norm_num.",
      190,
      Math.min(0.99, Number((0.93 + wfBoost).toFixed(2)))
    );
  }
  if (hasChannelOrPrior) {
    pushRec(
      "channel_fields",
      "channel-prior-constructor-obligations",
      "Constructs Channel or Prior and discharges nonneg and rowMass/mass obligations over Fin 1..8.",
      180,
      0.92
    );
  }
  const hasInductiveProof = /\b(?:cases|rcases|induction|constructor)\b/.test(proof);
  if (hasInductiveProof) {
    pushRec(
      "aesop",
      "whitebox-best-first-search",
      "Best-first search over safe/unsafe rulesets; replaces manual intro/case/constructor chains.",
      800,
      0.85
    );
  }
  if (/\bapply\b/.test(proof) && !hasInductiveProof) {
    pushRec(
      "solve_by_elim",
      "bounded-backtracking-unification",
      "Backtracking unification over local hypotheses without expanding external lemmas.",
      220,
      0.80
    );
  }
  if (
    /(?:\bFin\s+\d+|\bFinset\b|\bdecide\b|\btrue\b|\bfalse\b)/.test(target) &&
    !hasChannelOrPrior &&
    !hasWellFormed &&
    (!hasFinsetSumInTargetOrProof || /\b(?:decide|true|false)\b/.test(target))
  ) {
    pushRec(
      "decide",
      "decidable-proposition-evaluation",
      "Kernel reflection on Decidable instance; zero search branching.",
      80,
      0.95
    );
  }

  recommendations.sort((a, b) => a.estimatedHeartbeats - b.estimatedHeartbeats);

  const legibility = scoreAltProofLegibility(proof);
  const baselineLines = Math.max(1, legibility.steps);
  const baselineCostX10 = computeAltProofCostX10(baselineLines, 0, false, 0);

  let zoneDecreasingHint: string | undefined;
  if (/\b[A-Za-z_]\w*\s*-\s*\(\s*[A-Za-z_]\w*\s*\+\s*1\s*\)\s*<\s*[A-Za-z_]\w*\s*-\s*[A-Za-z_]\w*/.test(combined)) {
    const verdict = interpreter.checkZoneSubDecreasing(-1, 1);
    zoneDecreasingHint = `Zone DBM termination check (n - (i + 1) < n - i under i < n): ${verdict} (discharge via omega).`;
  }

  return {
    goal,
    features,
    relevantRoutes,
    recommendations,
    legibility,
    baselineCostX10,
    bestTactic: recommendations.length > 0 ? recommendations[0].tactic : null,
    bestEstimatedHeartbeats: recommendations.length > 0 ? recommendations[0].estimatedHeartbeats : 0,
    staticCertificates,
    zoneDecreasingHint,
    abstractCertification
  };
}



