// tests/test_decl_references.mjs
// Unit tests for .ilean `references` ingestion (Lean4IleanIndex.lookupReferences).
// Strict 7-bit ASCII only (INV-001).
//
// Regression origin: the .ilean reader consumed only `decls` and ignored the
// `references` map, so the index knew where a name was declared but not which
// constants it used - no lemma -> theorem edges, i.e. no declaration graph.
// The fixture below is the real Lean 4.33 .ilean shape:
//   references[<JSON {"c":{"m":<module>,"n":<name>}}>] = { definition, usages }
//   usages[i] = [startLine, startCol, endLine, endCol, <using declaration name>]

import assert from "node:assert";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { Lean4IleanIndex } from "../src/index.ts";

console.log("=== Testing .ilean declaration reference graph ===");

const root = fs.mkdtempSync(path.join(os.tmpdir(), "lean-ilean-"));
const libDir = path.join(root, ".lake", "build", "lib", "lean");
fs.mkdirSync(libDir, { recursive: true });

const specIlean = {
  version: 5,
  module: "Spec",
  decls: {
    helper: [2, 0, 4, 27],
    mainThm: [7, 0, 9, 40],
  },
  directImports: [["Init", false, false, false]],
  references: {
    // [0-9] = in-file constant (`definition` points into this file)
    [JSON.stringify({ c: { m: "Spec", n: "helper" } })]: {
      definition: [2, 0, 4, 27],
      usages: [[8, 10, 8, 16, "mainThm"]],
    },
    [JSON.stringify({ c: { m: "Init.Prelude", n: "Nat" } })]: {
      definition: null,
      usages: [
        [3, 14, 3, 17, "helper"],
        [8, 20, 8, 23, "mainThm"],
      ],
    },
    [JSON.stringify({ c: { m: "Init.Prelude", n: "Nat.add" } })]: {
      definition: null,
      usages: [[8, 30, 8, 37, "mainThm"]],
    },
    // An entry with no usages must not create a phantom edge.
    [JSON.stringify({ c: { m: "Init.Prelude", n: "Nat.zero" } })]: {
      definition: null,
      usages: [],
    },
    // Malformed key: skipped, never thrown.
    "not-json": { definition: null, usages: [[1, 1, 1, 2, "mainThm"]] },
  },
};

fs.writeFileSync(path.join(libDir, "Spec.ilean"), JSON.stringify(specIlean));
// The real source must exist for the index to map module -> file path.
fs.writeFileSync(path.join(root, "Spec.lean"), "def helper := 0\ntheorem mainThm : True := trivial\n");

const index = new Lean4IleanIndex(root);
// refresh() is expected to be cheap on a core project (measured 1-3 ms for the
// real 8-problem corpus); assert only that it terminates without throwing.
const t0 = Date.now();
index.refresh();
const refreshMs = Date.now() - t0;

// 1. `uses` from the using declaration's point of view.
{
  const uses = index.lookupReferences("mainThm", "uses", 50);
  assert.strictEqual(uses.resolved, true, "mainThm has reference edges");
  const text = uses.lines.join("\n");
  assert.ok(text.includes("Spec.helper"), `in-file lemma edge present, got: ${text}`);
  assert.ok(text.includes("Init.Prelude.Nat.add"), `imported constant edge present, got: ${text}`);
  assert.ok(!text.includes("Init.Prelude.Nat.zero"), `zero-usage entry creates no edge, got: ${text}`);
  assert.ok(!text.includes("not-json"), "malformed reference key is skipped");
  assert.strictEqual(uses.total, 3, `exactly 3 constants referenced by mainThm, got ${uses.total}`);
}

// 2. `usedBy` from the referenced constant's point of view (both declarations).
{
  const usedBy = index.lookupReferences("Init.Prelude.Nat", "usedBy", 50);
  assert.strictEqual(usedBy.resolved, true);
  const text = usedBy.lines.join("\n");
  assert.ok(text.includes("Spec.helper"), `helper uses Nat, got: ${text}`);
  assert.ok(text.includes("Spec.mainThm"), `mainThm uses Nat, got: ${text}`);
  assert.strictEqual(usedBy.total, 2);
}

// 3. Bare and module-qualified names both resolve; the file position is shown.
{
  const bare = index.lookupReferences("helper", "usedBy", 50);
  assert.strictEqual(bare.resolved, true, "bare name resolves");
  assert.ok(bare.lines.join("\n").includes("Spec.mainThm"));

  // The qualified form resolves in the `uses` direction (declToRefs stores both).
  const qualified = index.lookupReferences("Spec.mainThm", "uses", 50);
  assert.strictEqual(qualified.resolved, true, "module-qualified name resolves");
  assert.strictEqual(qualified.total, 3, "qualified and bare names give the same edges");

  // A declaration nothing references is honestly empty in the usedBy direction.
  const selfOnly = index.lookupReferences("Spec.mainThm", "usedBy", 50);
  assert.strictEqual(selfOnly.resolved, false, "unreferenced declaration has no usedBy edges");

  // Spec.helper is declared in-file, so describe() must add its position.
  const withPosition = index.lookupReferences("mainThm", "uses", 50).lines.join("\n");
  assert.ok(/Spec\.helper \([^)]*:3\)/.test(withPosition), `position annotated, got: ${withPosition}`);
  assert.ok(withPosition.includes("Spec.lean:3"), `source file, not the .ilean, got: ${withPosition}`);
}

// 4. `both` merges directions; limit truncates with an explicit remainder.
{
  const both = index.lookupReferences("mainThm", "both", 1);
  const text = both.lines.join("\n");
  assert.ok(text.includes("uses (3 constant(s)):"), `uses header, got: ${text}`);
  assert.ok(text.includes("... 2 more"), `limit truncation is explicit, got: ${text}`);
}

// 5. Unknown symbol: honest answer, no fabricated edges.
{
  const missing = index.lookupReferences("doesNotExist", "both", 5);
  assert.strictEqual(missing.resolved, false);
  assert.ok(missing.lines.join("\n").includes("no reference edges recorded"));
}

// 6. A project whose .ilean files carry no `references` map degrades cleanly.
{
  const bare = fs.mkdtempSync(path.join(os.tmpdir(), "lean-ilean-noref-"));
  const dir = path.join(bare, ".lake", "build", "lib", "lean");
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(
    path.join(dir, "Old.ilean"),
    JSON.stringify({ version: 4, module: "Old", decls: { only: [0, 0, 1, 10] } })
  );
  const oldIndex = new Lean4IleanIndex(bare);
  oldIndex.refresh();
  const result = oldIndex.lookupReferences("only", "both", 5);
  assert.strictEqual(result.resolved, false, "no references map => no edges, not a crash");
  assert.ok(result.lines.join("\n").includes("no reference edges recorded"));
  fs.rmSync(bare, { recursive: true, force: true });
}

fs.rmSync(root, { recursive: true, force: true });
console.log(`  - refresh on the fixture: ${refreshMs} ms`);
console.log("=== .ilean declaration reference suite: ALL PASS ===");
