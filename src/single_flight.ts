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
 * lives as long as the instance). A wedged flight holds its key until
 * the process ends; an owner that needs a deadline wraps fn.
 *
 * Strict 7-bit ASCII only (INV-001).
 */

export interface SingleFlight<T> {
  run(key: string, fn: () => Promise<T>): Promise<T>;
  clear(): void;
  inFlightCount(): number;
}

export function createSingleFlight<T>(): SingleFlight<T> {
  const inflight = new Map<string, Promise<T>>();
  return {
    run(key: string, fn: () => Promise<T>): Promise<T> {
      const existing = inflight.get(key);
      if (existing) return existing;
      const flight = fn().finally(() => {
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
