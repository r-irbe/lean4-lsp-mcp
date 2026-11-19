import assert from "node:assert/strict";
import { test } from "node:test";
import { KuzuKnowledgeGraph } from "../src/kuzu_graph.ts";

function graphFixture() {
  const graph = new KuzuKnowledgeGraph("/tmp/unused-short-query-fixture.kz");
  // Isolate retrieval from archive transport; public maps represent loaded rows.
  graph.load = () => true;
  graph.books.set("smt", { key: "smt", title: "SMT References" });
  graph.sections.set("z3-api", { id: "z3-api", bookKey: "smt", level: 1, title: "Z3 solver API" });
  graph.sections.set("cvc5-api", { id: "cvc5-api", bookKey: "smt", level: 1, title: "cvc5 solver API" });
  graph.sections.set("f2-fields", { id: "f2-fields", bookKey: "smt", level: 1, title: "F2 / F₂ finite fields" });
  return graph;
}

test("section retrieval retains short letter-digit technical names", () => {
  const graph = graphFixture();
  assert.deepEqual(graph.search("Z3").map((r) => r.sectionId), ["z3-api"]);
  assert.deepEqual(graph.search("z3").map((r) => r.sectionId), ["z3-api"]);
  assert.deepEqual(graph.search("F2").map((r) => r.sectionId), ["f2-fields"]);
  assert.deepEqual(graph.search("F₂").map((r) => r.sectionId), ["f2-fields"]);
});

test("mixed queries count the technical name rather than silently dropping it", () => {
  const results = graphFixture().search("Z3 solver");
  assert.deepEqual(results.map((r) => [r.sectionId, r.score]), [["z3-api", 1], ["cvc5-api", 0.5]]);
});

test("long-term retrieval, result limit and short noise behavior remain intact", () => {
  const graph = graphFixture();
  assert.deepEqual(graph.search("solver", 1).map((r) => r.sectionId), ["z3-api"]);
  assert.deepEqual(graph.search("of"), []);
  assert.deepEqual(graph.search("9"), []);
  assert.deepEqual(graph.search("42"), []);
  assert.deepEqual(graph.search("  "), []);
});
