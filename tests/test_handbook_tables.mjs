// tests/test_handbook_tables.mjs
// Regression tests for the handbook-tables.v1.json integration:
//   - lean_search source="handbook" searches intent_phrasebook / error_to_fix /
//     goal_shape_templates with book-filter and limit support
//   - lean_cross_itp_concordance falls back to handbook rows when neither the
//     concordance table, the master authority index, nor book indexes match
//   - the vendored copy stays byte-identical to the pi-lens canonical asset
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import { McpServer } from "../src/index.ts";

console.log("Running Handbook Tables Integration Test Suite...");

const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "lean-handbook-test-"));
const server = new McpServer(tmpDir);

// 1. source="handbook": intent phrasebook hit (HOL ARITH_TAC -> omega)
{
  const out = await server.executeTool("lean_search", { query: "ARITH_TAC", source: "handbook" });
  assert.ok(out.includes("Handbook table matches"), "handbook search returns matches header");
  assert.ok(out.includes("intent_phrasebook"), "match is labeled with its table");
  assert.ok(out.includes("omega"), "ARITH_TAC intent maps to the omega tactic");
  console.log("  - lean_search source=handbook intent_phrasebook hit: PASS");
}

// 2. source="handbook": error_to_fix hit with cause and fix lines
{
  const out = await server.executeTool("lean_search", {
    query: "truncates",
    source: "handbook",
  });
  assert.ok(out.includes("error_to_fix"), "error table match is labeled");
  assert.ok(out.includes("fix:"), "error match carries a deterministic fix");
  console.log("  - lean_search source=handbook error_to_fix hit: PASS");
}

// 3. source="handbook": goal_shape_templates hit
{
  const out = await server.executeTool("lean_search", {
    query: "INDUCT_TAC",
    source: "handbook",
  });
  assert.ok(out.includes("goal_shape_templates"), "goal shape match is labeled");
  assert.ok(out.includes("induction"), "HOL INDUCT_TAC maps to a Lean induction template");
  console.log("  - lean_search source=handbook goal_shape_templates hit: PASS");
}

// 4. book filter narrows handbook rows
{
  const out = await server.executeTool("lean_search", {
    query: "omega",
    source: "handbook",
    book: "hol-metamath",
  });
  assert.ok(out.includes("hol-metamath-adapter-handbook"), "book filter keeps matching handbook");
  const filteredOut = await server.executeTool("lean_search", {
    query: "omega",
    source: "handbook",
    book: "no-such-handbook-xyz",
  });
  assert.ok(filteredOut.includes("No handbook table matches"), "unknown book filter yields a clean miss");
  console.log("  - lean_search source=handbook book filter: PASS");
}

// 5. limit is honored
{
  const out = await server.executeTool("lean_search", { query: "the", source: "handbook", limit: 2 });
  const dashLines = out.split("\n").filter((l) => l.startsWith("- ["));
  assert.ok(dashLines.length <= 2, `limit=2 caps result rows (got ${dashLines.length})`);
  console.log("  - lean_search source=handbook limit: PASS");
}

// 6. concordance fallback reaches handbook rows for idioms absent from the
//    canonical concordance (verified: "chiseling" appears only in the
//    lean-causal-reasoning handbook error_to_fix table).
{
  const out = await server.executeTool("lean_cross_itp_concordance", { concept: "chiseling" });
  assert.ok(out.includes("[handbook:"), "concordance fallback surfaces handbook rows");
  assert.ok(out.includes("lean-causal-reasoning-handbook"), "handbook fallback row names its handbook");
  console.log("  - lean_cross_itp_concordance handbook fallback: PASS");
}

// 7. concordance fallback clean miss keeps the existing message
{
  const out = await server.executeTool("lean_cross_itp_concordance", { concept: "zzz-no-such-concept" });
  assert.ok(out.includes("No concordance entry"), "clean miss message preserved");
  console.log("  - lean_cross_itp_concordance clean miss: PASS");
}

// 8. existing concordance results are unchanged by the fallback (induction
//    resolves via the canonical table, not the handbook).
{
  const out = await server.executeTool("lean_cross_itp_concordance", { concept: "induction" });
  assert.ok(out.includes("CONC-01-CASE-INDUCTION"), "canonical concordance entry still wins");
  assert.ok(!out.includes("[handbook:"), "handbook fallback does not fire when canonical matches exist");
  console.log("  - canonical concordance precedence preserved: PASS");
}

// 9. vendored copy is byte-identical to the pi-lens canonical asset (when
//    the sibling checkout exists), guarding against divergent copies.
{
  const piLensCopy = "/home/radu/code/pi-lens/vendor/itp-ontology/handbook-tables.v1.json";
  const localCopy = path.resolve(import.meta.dirname, "../data/itp-ontology/handbook-tables.v1.json");
  assert.ok(fs.existsSync(localCopy), "vendored handbook-tables.v1.json exists");
  if (fs.existsSync(piLensCopy)) {
    assert.strictEqual(
      fs.readFileSync(localCopy, "utf-8"),
      fs.readFileSync(piLensCopy, "utf-8"),
      "vendored handbook tables must stay byte-identical to the pi-lens canonical copy"
    );
  }
  console.log("  - vendored handbook copy byte-identical to pi-lens canonical: PASS");
}

console.log("All Handbook Tables Integration tests PASSED!");
process.exit(0);
