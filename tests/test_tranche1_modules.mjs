// tests/test_tranche1_modules.mjs
// Unit lane for the pi-lens tranche-1 port: content limits and the
// single-flight primitive. Strict 7-bit ASCII only (INV-001).

import assert from "node:assert/strict";
import { exceedsLspContentLimits, ContentLimitError, contentLimitBounds } from "../src/content_limits.ts";
import { createSingleFlight } from "../src/single_flight.ts";

// --- content limits ---

{
  const v = exceedsLspContentLimits("import Lake\n");
  assert.equal(v.exceeded, false);
  assert.equal(v.lines, 2);
}

{
  // over the line bound: 100_000 default + 1
  const { limitLines } = contentLimitBounds();
  const big = Array.from({ length: limitLines + 1 }, () => "x").join("\n");
  const v = exceedsLspContentLimits(big);
  assert.equal(v.exceeded, true);
  assert.ok(v.lines > v.limitLines);
}

{
  // the env override is honored (positive integers only)
  process.env.LSP_CONTENT_LIMIT_LINES = "10";
  const v = exceedsLspContentLimits("a\nb\nc\nd\ne\nf\ng\nh\ni\nj\nk\n");
  assert.equal(v.exceeded, true);
  assert.equal(v.limitLines, 10);
  delete process.env.LSP_CONTENT_LIMIT_LINES;
  const v2 = exceedsLspContentLimits("a\nb\nc\n");
  assert.equal(v2.exceeded, false);
}

{
  // garbage env values fall back to the defaults
  process.env.LSP_CONTENT_LIMIT_LINES = "not-a-number";
  assert.equal(contentLimitBounds().limitLines, 100_000);
  process.env.LSP_CONTENT_LIMIT_LINES = "-5";
  assert.equal(contentLimitBounds().limitLines, 100_000);
  delete process.env.LSP_CONTENT_LIMIT_LINES;
}

{
  const err = new ContentLimitError("too big");
  assert.ok(err instanceof Error);
  assert.equal(err.name, "ContentLimitError");
}

// --- single flight ---

{
  // share: two concurrent runs on one key execute fn once
  let calls = 0;
  const sf = createSingleFlight();
  const p1 = sf.run("k", async () => { calls += 1; return "v"; });
  const p2 = sf.run("k", async () => { calls += 1; return "other"; });
  const [r1, r2] = await Promise.all([p1, p2]);
  assert.equal(calls, 1);
  assert.equal(r1, "v");
  assert.equal(r2, "v");
  assert.equal(sf.inFlightCount(), 0);
}

{
  // finally-clear: after a settle, a new run re-executes
  let calls = 0;
  const sf = createSingleFlight();
  await sf.run("k", async () => { calls += 1; });
  await sf.run("k", async () => { calls += 1; });
  assert.equal(calls, 2);
}

{
  // pi-lens #1674 class: the owner's clear() between an old flight settling
  // and its finally must not let the old flight evict the replacement.
  let release1;
  const sf = createSingleFlight();
  const p1 = sf.run("k", () => new Promise((res) => { release1 = res; }));
  sf.clear();                                          // the owner's session reset
  let release2;
  const p2 = sf.run("k", () => new Promise((res) => { release2 = res; }));
  release1("first");                                   // the old flight settles
  assert.equal(await p1, "first");                      // its finally runs here
  assert.equal(sf.inFlightCount(), 1, "the replacement must still own the key");
  release2("replacement");                              // the replacement settles
  assert.equal(await p2, "replacement");
}

{
  // clear(): the owner's reset seam empties the registry
  const sf = createSingleFlight();
  let release;
  sf.run("k", () => new Promise((res) => { release = res; }));
  assert.equal(sf.inFlightCount(), 1);
  sf.clear();
  assert.equal(sf.inFlightCount(), 0);
  release("orphan");
}

// distinct keys never share
{
  let calls = 0;
  const sf = createSingleFlight();
  await Promise.all([
    sf.run("a", async () => { calls += 1; }),
    sf.run("b", async () => { calls += 1; }),
  ]);
  assert.equal(calls, 2);
}

console.log("tranche1 modules: ALL PASS");

// --- tranche 3: the bounded cache ---

{
  const { BoundedCache } = await import("../src/bounded_cache.ts");
  const c = new BoundedCache({ maxEntries: 2, ttlMs: 60_000 });
  c.set("a", "1");
  c.set("b", "2");
  assert.equal(c.get("a"), "1");
  c.set("c", "3");                      // evicts the LRU ("a" was touched after "b"? no: a then b -> LRU is a... a was got, so b is LRU)
  assert.equal(c.get("b"), undefined, "the LRU entry is evicted");
  assert.equal(c.get("a"), "1", "the touched entry survives");
  assert.equal(c.get("c"), "3");
}

{
  const { BoundedCache } = await import("../src/bounded_cache.ts");
  const c = new BoundedCache({ maxEntries: 10, ttlMs: 30 });
  c.set("k", "v");
  assert.equal(c.get("k"), "v");
  await new Promise((r) => setTimeout(r, 50));
  assert.equal(c.get("k"), undefined, "the TTL expires the entry");
}
console.log("bounded cache: PASS");
