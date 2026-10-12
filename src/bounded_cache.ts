/**
 * bounded_cache.ts - a bounded LRU with per-entry TTL for the
 * read-mostly search-family tools (pi-lens tranche-3 port, in-process
 * form; the on-disk variant is deferred until a cross-restart need
 * materializes).
 *
 * Strict 7-bit ASCII only (INV-001).
 */

export interface BoundedCacheOptions {
  maxEntries?: number;
  ttlMs?: number;
}

interface Entry<T> {
  value: T;
  expiresAt: number;
}

export class BoundedCache<T> {
  private max: number;
  private ttl: number;
  private map = new Map<string, Entry<T>>();

  constructor(options: BoundedCacheOptions = {}) {
    this.max = options.maxEntries ?? 128;
    this.ttl = options.ttlMs ?? 10 * 60_000;
  }

  get(key: string): T | undefined {
    const e = this.map.get(key);
    if (!e) return undefined;
    if (Date.now() > e.expiresAt) {
      this.map.delete(key);
      return undefined;
    }
    // LRU touch: re-insert to move to the map's tail (the recency end)
    this.map.delete(key);
    this.map.set(key, e);
    return e.value;
  }

  set(key: string, value: T): void {
    if (this.map.has(key)) this.map.delete(key);
    this.map.set(key, { value, expiresAt: Date.now() + this.ttl });
    while (this.map.size > this.max) {
      // the map's first key is the least recently used
      const lru = this.map.keys().next().value;
      if (lru === undefined) break;
      this.map.delete(lru);
    }
  }

  clear(): void {
    this.map.clear();
  }

  get size(): number {
    return this.map.size;
  }
}
