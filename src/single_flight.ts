/**
 * single_flight.ts - at most one execution per key, cleared in finally.
 *
 * Ported from the pi-lens fork's clients/single-flight.ts (the core of
 * its intersection API: share + clear-in-finally; the trailing-rerun
 * and generation options stay at pi-lens's sites, which need them).
 *
 * Motivation here: under the shared lake-serve broker
 * (CONV-LEAN-SERVE-SINGLETON), two MCP clients can issue identical
 * in-flight read-only requests against the one language server; one
 * execution per (key) saves the duplicate elaboration wait.
 *
 * LIFECYCLE: the primitive owns no module state - createSingleFlight
 * returns a closure whose lifetime is its owner's (an instance field
 * lives as long as the instance). An owner that needs a deadline wraps
 * fn; one that wants a guard-side bound passes settleBudgetMs, so a
 * never-settling fn cannot pin the key (and every future caller) until
 * the process ends - adopted from the pi-lens #2939 M10 pin: the guard
 * bounds the flight, not the owner's goodwill. On budget expiry the
 * caller sees FlightBudgetError and the key releases; the late original
 * still settles through its own finally, which must not evict a
 * post-budget replacement (the #1674 ordering rule).
 *
 * Strict 7-bit ASCII only (INV-001).
 */

export class FlightBudgetError extends Error {
  readonly budgetMs: number;
  constructor(key: string, budgetMs: number) {
    super(`single-flight budget exceeded (${budgetMs}ms) for key "${key}"`);
    this.name = "FlightBudgetError";
    this.budgetMs = budgetMs;
  }
}

export interface SingleFlightOptions {
  /** Guard-side settle budget in milliseconds (M10). */
  settleBudgetMs?: number;
}

export interface SingleFlight<T> {
  run(key: string, fn: () => Promise<T>): Promise<T>;
  clear(): void;
  inFlightCount(): number;
}

export function createSingleFlight<T>(
  options: SingleFlightOptions = {}
): SingleFlight<T> {
  const budgetMs = options.settleBudgetMs;
  const inflight = new Map<string, Promise<T>>();
  return {
    run(key: string, fn: () => Promise<T>): Promise<T> {
      const existing = inflight.get(key);
      if (existing) return existing;
      let base = fn();
      if (budgetMs !== undefined) {
        const raced = Promise.race([
          base,
          new Promise<never>((_, reject) => {
            // an ordinary timer on purpose: unref would let a draining
            // event loop die before the guard fires - a wedged flight is
            // exactly a reason to keep the process alive
            setTimeout(() => reject(new FlightBudgetError(key, budgetMs)), budgetMs);
          }),
        ]);
        // when the budget loses the race, base's later settlement would
        // be unobserved; keep it from surfacing as an unhandled rejection
        base.catch(() => {});
        base = raced;
      }
      const flight = base.finally(() => {
        // clear only if this flight still owns the key: a replacement
        // flight started by a finally-ordered race must not be evicted
        if (inflight.get(key) === flight) inflight.delete(key);
      });
      inflight.set(key, flight);
      return flight;
    },
    clear(): void {
      inflight.clear();
    },
    inFlightCount(): number {
      return inflight.size;
    },
  };
}
