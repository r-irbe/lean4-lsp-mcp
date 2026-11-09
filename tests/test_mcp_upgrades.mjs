// tests/test_mcp_upgrades.mjs
// Regression tests for:
// 1. In-process node:zlib ZIP reader for Kuzu .kz archives + Concept/Zettel graph search
// 2. BitsetDAGIndex bounded-depth longest-path reachability on diamond DAGs
// 3. Lean4IleanIndex multi-root Lake discovery + (mtimeMs, size) parse cache + in-place edit detection
// 4. lean_server_status text + JSON introspection (gitSha, wasmArtifact, toolchain, lakeRoots, ileanCache)
// 5. lean_exec timeoutMs + Core-only Mathlib tactic failure hints
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import zlib from "node:zlib";
import { test } from "node:test";
import { KuzuKnowledgeGraph, readZipEntries } from "../src/kuzu_graph.ts";
import { BitsetDAGIndex, Lean4IleanIndex, McpServer } from "../src/index.ts";
import { explainLeanFailure } from "../src/project_root.ts";

function buildTestZipBuffer(entries) {
  const localParts = [];
  const centralParts = [];
  let offset = 0;

  for (const entry of entries) {
    const nameBuf = Buffer.from(entry.name, "utf-8");
    const rawBuf = Buffer.from(entry.content, "utf-8");
    const method = entry.deflate ? 8 : 0;
    const dataBuf = entry.deflate ? zlib.deflateRawSync(rawBuf) : rawBuf;

    const localHdr = Buffer.alloc(30);
    localHdr.writeUInt32LE(0x04034b50, 0);
    localHdr.writeUInt16LE(20, 4);
    localHdr.writeUInt16LE(0, 6);
    localHdr.writeUInt16LE(method, 8);
    localHdr.writeUInt32LE(0, 10);
    localHdr.writeUInt32LE(0, 14);
    localHdr.writeUInt32LE(dataBuf.length, 18);
    localHdr.writeUInt32LE(rawBuf.length, 22);
    localHdr.writeUInt16LE(nameBuf.length, 26);
    localHdr.writeUInt16LE(0, 28);
    localParts.push(localHdr, nameBuf, dataBuf);

    const centralHdr = Buffer.alloc(46);
    centralHdr.writeUInt32LE(0x02014b50, 0);
    centralHdr.writeUInt16LE(20, 4);
    centralHdr.writeUInt16LE(20, 6);
    centralHdr.writeUInt16LE(0, 8);
    centralHdr.writeUInt16LE(method, 10);
    centralHdr.writeUInt32LE(0, 12);
    centralHdr.writeUInt32LE(0, 16);
    centralHdr.writeUInt32LE(dataBuf.length, 20);
    centralHdr.writeUInt32LE(rawBuf.length, 24);
    centralHdr.writeUInt16LE(nameBuf.length, 28);
    centralHdr.writeUInt16LE(0, 30);
    centralHdr.writeUInt16LE(0, 32);
    centralHdr.writeUInt16LE(0, 34);
    centralHdr.writeUInt16LE(0, 36);
    centralHdr.writeUInt32LE(0, 38);
    centralHdr.writeUInt32LE(offset, 42);
    centralParts.push(centralHdr, nameBuf);

    offset += localHdr.length + nameBuf.length + dataBuf.length;
  }

  const centralBuf = Buffer.concat(centralParts);
  const eocd = Buffer.alloc(22);
  eocd.writeUInt32LE(0x06054b50, 0);
  eocd.writeUInt16LE(0, 4);
  eocd.writeUInt16LE(0, 6);
  eocd.writeUInt16LE(entries.length, 8);
  eocd.writeUInt16LE(entries.length, 10);
  eocd.writeUInt32LE(centralBuf.length, 12);
  eocd.writeUInt32LE(offset, 16);
  eocd.writeUInt16LE(0, 20);

  return Buffer.concat([...localParts, centralBuf, eocd]);
}

test("KuzuKnowledgeGraph loads deflated and stored .kz entries in-process without unzip on PATH", async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "kuzu-zip-test-"));
  const origPath = process.env.PATH;
  try {
    const kzFile = path.join(tmpDir, "test_graph.kz");
    const zipBuf = buildTestZipBuffer([
      {
        name: "Book.csv",
        deflate: true,
        content: "key,title,license,sourceFormat\nbk1,Theorem Proving in Lean 4,CC-BY,Markdown\n",
      },
      {
        name: "Section.csv",
        deflate: true,
        content: "id,book_key,level,title\nsec1,bk1,2,Galois Connections and Lattices\n",
      },
      {
        name: "Concept.csv",
        deflate: true,
        content: "id,name,msc2020,domainTheory\nc_galois,GaloisInsertion,06A15,order_theory\n",
      },
      {
        name: "Zettel.csv",
        deflate: false,
        content: "id,title,layer,status,c4,c5,sourceBook,sourceAnchor,masterConcept,filePath\nzt_101,Galois Kernel Reduction Law,4,verified,x,y,bk1,sec1,c_galois,Kernel/Galois.lean\n",
      },
    ]);
    fs.writeFileSync(kzFile, zipBuf);

    // Verify readZipEntries directly
    const map = readZipEntries(zipBuf, new Set(["Book.csv", "Concept.csv", "Zettel.csv"]));
    assert.equal(map.size, 3);
    assert.match(map.get("Concept.csv")?.toString("utf-8") || "", /GaloisInsertion/);

    // Empty PATH so any external `unzip` spawn would fail
    process.env.PATH = "";
    const kg = new KuzuKnowledgeGraph(kzFile);
    const secs = kg.search("galois", 5);
    assert.equal(secs.length, 1);
    assert.equal(secs[0].sectionId, "sec1");

    const concepts = kg.searchConcepts("galois", 5);
    assert.equal(concepts.length, 1);
    assert.equal(concepts[0].id, "c_galois");

    const zettels = kg.searchZettels("galois", 5);
    assert.equal(zettels.length, 1);
    assert.equal(zettels[0].id, "zt_101");

    // Verify lean_search(source="graph") surfaces Sections, Concepts, and Zettels
    process.env.PATH = origPath;
    const server = new McpServer(tmpDir);
    server.kuzuGraph = kg;
    const graphOut = await server.executeTool("lean_search", {
      query: "galois",
      source: "graph",
      limit: 5,
    });
    assert.match(graphOut, /Section: sec1/);
    assert.match(graphOut, /Concept: c_galois/);
    assert.match(graphOut, /Zettel: zt_101/);
  } finally {
    process.env.PATH = origPath;
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});

test("BitsetDAGIndex.getTransitiveClosure computes exact bounded longest-path depth on diamond DAGs", () => {
  const dag = new BitsetDAGIndex();
  // Diamond with extension:
  // Root -> X -> Y (length 2 to Y)
  // Root -> Y -> W (length 2 to W via Y!)
  // Under maxDepth = 2, W is reachable via Root -> Y -> W (depth 2) AND Root -> X -> Y (depth 2).
  // Previously Kahn DP saturated Y at depth 2 via Root -> X -> Y and refused to relax Y -> W, leaving W at 0.
  const imports = new Map([
    ["Root", ["X", "Y"]],
    ["X", ["Y"]],
    ["Y", ["W"]],
    ["W", ["Z"]],
    ["Z", []],
  ]);
  dag.build(imports);
  dag.precomputeClosureMatrix();

  const bounded2 = dag.getTransitiveClosure("Root", "imports", 2);
  assert.deepEqual(bounded2.items.sort(), ["W", "X", "Y"]);
  assert.equal(bounded2.depth, 2);
  assert.equal(bounded2.hasCycle, false);

  const unbounded = dag.getTransitiveClosure("Root", "imports", 20);
  assert.deepEqual(unbounded.items.sort(), ["W", "X", "Y", "Z"]);
  assert.equal(unbounded.depth, 4);
  assert.equal(unbounded.hasCycle, false);
});

test("Lean4IleanIndex discovers subproject + LEAN_LAKE_ROOTS .ilean trees and caches unchanged files by (mtimeMs, size)", () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "ilean-multiroot-"));
  const prevEnv = process.env.LEAN_LAKE_ROOTS;
  try {
    const wsRoot = path.join(tmpDir, "ws");
    fs.mkdirSync(wsRoot, { recursive: true });
    fs.writeFileSync(path.join(wsRoot, "AGENTS.md"), "# ws\n");

    // Subproject under wsRoot/sub/probA with lakefile.toml
    const probA = path.join(wsRoot, "sub", "probA");
    const probAIleanDir = path.join(probA, ".lake", "build", "lib", "lean");
    fs.mkdirSync(probAIleanDir, { recursive: true });
    fs.writeFileSync(path.join(probA, "lakefile.toml"), 'name = "probA"\n');
    const ileanA = path.join(probAIleanDir, "ProbA.ilean");
    fs.writeFileSync(
      ileanA,
      JSON.stringify({ module: "ProbA", decls: { symProbA: [0, 0, 1, 1] }, directImports: [] })
    );

    // External root via LEAN_LAKE_ROOTS
    const extRoot = path.join(tmpDir, "extLake");
    const extIleanDir = path.join(extRoot, ".lake", "build", "lib", "lean");
    fs.mkdirSync(extIleanDir, { recursive: true });
    fs.writeFileSync(
      path.join(extIleanDir, "ExtMod.ilean"),
      JSON.stringify({ module: "ExtMod", decls: { symExtMod: [2, 0, 3, 1] }, directImports: [] })
    );
    process.env.LEAN_LAKE_ROOTS = extRoot;

    const index = new Lean4IleanIndex(wsRoot);
    index.refresh();

    assert.ok(index.lookupSymbol("symProbA"), "Expected subproject symbol symProbA to be indexed");
    assert.ok(index.lookupSymbol("symExtMod"), "Expected LEAN_LAKE_ROOTS symbol symExtMod to be indexed");
    const rep1 = index.getScanReport();
    assert.equal(rep1.scannedFiles, 2);
    assert.equal(rep1.cacheHits, 0);
    assert.equal(rep1.cacheMisses, 2);

    // Second refresh without file modifications should hit parsedFileCache 100%
    index.refresh();
    const rep2 = index.getScanReport();
    assert.equal(rep2.scannedFiles, 2);
    assert.equal(rep2.cacheHits, 2);
    assert.equal(rep2.cacheMisses, 0);
    assert.equal(index.hasNewerBuilds(), false);

    // In-place overwrite of ileanA (changing size/content without touching directory entries)
    fs.writeFileSync(
      ileanA,
      JSON.stringify({
        module: "ProbA",
        decls: { symProbA: [0, 0, 1, 1], symProbAUpdated: [4, 0, 5, 1] },
        directImports: [],
      })
    );
    assert.equal(index.hasNewerBuilds(), true, "In-place .ilean modification must be detected by hasNewerBuilds()");
    index.refresh();
    const rep3 = index.getScanReport();
    assert.equal(rep3.cacheHits, 1);
    assert.equal(rep3.cacheMisses, 1);
    assert.ok(index.lookupSymbol("symProbAUpdated"));
  } finally {
    if (prevEnv === undefined) delete process.env.LEAN_LAKE_ROOTS;
    else process.env.LEAN_LAKE_ROOTS = prevEnv;
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});

test("lean_server_status supports text and json introspection and explainLeanFailure hints Core-only Mathlib tactics", async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "server-status-"));
  try {
    fs.writeFileSync(path.join(tmpDir, "lakefile.toml"), 'name = "demo"\n');
    fs.writeFileSync(path.join(tmpDir, "lean-toolchain"), "leanprover/lean4:v4.28.0\n");

    const server = new McpServer(tmpDir);
    const textStatus = await server.executeTool("lean_server_status", {});
    assert.match(textStatus, /mcp gitSha:/);
    assert.match(textStatus, /wasm artifact: \d+ bytes/);
    assert.match(textStatus, /toolchain: leanprover\/lean4:v4\.28\.0/);

    const jsonStatus = JSON.parse(await server.executeTool("lean_server_status", { format: "json" }));
    assert.equal(jsonStatus.toolchain, "leanprover/lean4:v4.28.0");
    assert.ok(jsonStatus.wasmArtifact.sizeBytes > 0 && jsonStatus.wasmArtifact.sizeBytes <= 131072);
    assert.ok(Array.isArray(jsonStatus.lakeRoots));

    // Core-only tactic failure hints
    const dummyInvocation = {
      command: "lean",
      args: ["--stdin"],
      cwd: tmpDir,
      root: tmpDir,
      via: "bare",
    };
    const ringHint = explainLeanFailure("error: unknown tactic 'ring'", dummyInvocation);
    assert.match(ringHint, /Mathlib tactic not imported in this environment|Mathlib tactic unavailable in Core-only/);
    assert.match(ringHint, /omega/);

    const normNumHint = explainLeanFailure("error: unknown tactic 'norm_num'", dummyInvocation);
    assert.match(normNumHint, /decide \+kernel/);

    // Negative control: normal unsolved goals must still return empty string
    assert.equal(explainLeanFailure("error: unsolved goals\n|- True", dummyInvocation), "");
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});
