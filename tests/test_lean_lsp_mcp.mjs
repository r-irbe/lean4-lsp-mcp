// tools/lean_lsp_mcp/tests/test_lean_lsp_mcp.mjs
// Unit and integration test suite for lean-lsp-mcp standalone module
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert";
import { spawn } from "node:child_process";
import * as path from "node:path";
import * as os from "node:os";
import { fileURLToPath } from "node:url";
import {
    Lean4IleanIndex,
    LeanSysrootBridge,
    formatGoalAsMarkdown,
    McpServer,
    TOOL_DEFINITIONS,
} from "../src/index.ts";

import * as fs from "node:fs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
const repoRoot = process.env.LEAN_PROJECT_ROOT || pkgRoot;

console.log("=== Testing lean4-lsp-mcp Suite ===");

// 1. formatGoalAsMarkdown
{
    const emptyGoal = formatGoalAsMarkdown("");
    assert.strictEqual(
        emptyGoal,
        "No active goals (proof complete or out of tactic scope).",
        "Empty goal string returns proof complete message"
    );

    const activeGoal = formatGoalAsMarkdown("case intro\nx : Nat\n|- x + 0 = x");
    assert.strictEqual(
        activeGoal,
        "```lean\ncase intro\nx : Nat\n|- x + 0 = x\n```",
        "Active goal formatted with lean markdown block"
    );
    console.log("  - formatGoalAsMarkdown: PASS");
}

// 2. LeanSysrootBridge
{
    const flags = LeanSysrootBridge.getIncludeFlags();
    assert(Array.isArray(flags), "Flags is an array");
    if (flags.length > 0) {
        assert(flags[0].startsWith("-I"), "First flag starts with -I");
        assert(flags.some(f => f.includes("include")), "Contains include directory");
    }
    const ffiReport = LeanSysrootBridge.inspectFFI(repoRoot, "nonexistent_extern");
    assert(ffiReport.includes("Lean 4 C FFI Environment"), "FFI report contains header");
    console.log("  - LeanSysrootBridge: PASS");
}

// 3. Lean4IleanIndex
{
    const index = new Lean4IleanIndex(repoRoot);
    const missing = index.lookupSymbol("NonExistentSymbol12345");
    assert.strictEqual(missing, null, "Missing symbol lookup returns null");
    console.log("  - Lean4IleanIndex: PASS");
}

// 4. McpServer Protocol Handlers (In-memory)
{
    const server = new McpServer(repoRoot);

    const initRes = await server.handleMessage({
        jsonrpc: "2.0",
        id: 1,
        method: "initialize",
        params: {
            protocolVersion: "2024-11-05",
            capabilities: {},
            clientInfo: { name: "test-client", version: "1.0.0" },
        },
    });
    assert(initRes && initRes.result.serverInfo.name === "lean-lsp-mcp", "initialize response ok");

    const listRes = await server.handleMessage({
        jsonrpc: "2.0",
        id: 2,
        method: "tools/list",
    });
    assert(listRes && Array.isArray(listRes.result.tools), "tools list is array");
    const toolNames = listRes.result.tools.map(t => t.name);
    assert.strictEqual(toolNames.length, 7, "Exposes exactly 7 consolidated tools (6 + the lean_resync recovery verb)");

    const expectedTools = ["lean_goal", "lean_search", "lean_blueprint", "lean_metrics", "lean_ffi", "lean_exec", "lean_resync"];
    for (const t of expectedTools) {
        assert(toolNames.includes(t), `Includes consolidated tool: ${t}`);
    }

    // Consolidated lean_search: graph source (Kuzu)
    const callKuzu = await server.handleMessage({
        jsonrpc: "2.0",
        id: 3,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "inductive proof", source: "graph", limit: 5 },
        },
    });
    assert(callKuzu && callKuzu.result && !callKuzu.result.isError, "Kuzu graph search succeeds");
    assert(callKuzu.result.content[0].text.includes("Section:"), "Kuzu graph returns indexed section results");

    // Consolidated lean_blueprint: graph_neighborhood (Kuzu)
    const callKuzuNeigh = await server.handleMessage({
        jsonrpc: "2.0",
        id: 4,
        method: "tools/call",
        params: {
            name: "lean_blueprint",
            arguments: { action: "graph_neighborhood", sectionId: "COQART s13.1 p1" },
        },
    });
    assert(callKuzuNeigh && callKuzuNeigh.result && !callKuzuNeigh.result.isError, "Kuzu graph neighborhood succeeds");
    assert(callKuzuNeigh.result.content[0].text.includes("Neighborhood:"), "Kuzu neighborhood returns formatted section");

    // Consolidated lean_search: ontology source
    const callOnto = await server.handleMessage({
        jsonrpc: "2.0",
        id: 5,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "liquid", source: "ontology" },
        },
    });
    assert(callOnto && callOnto.result && callOnto.result.content[0].text.includes("CONCEPT-CONDENSED-MATHEMATICS-LIQUID-VECTOR-SPACES"), "Ontology search resolves concept");

    // Consolidated lean_search: book source
    const callBook = await server.handleMessage({
        jsonrpc: "2.0",
        id: 6,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "category", source: "book" },
        },
    });
    assert(callBook && callBook.result && callBook.result.content[0].text.includes("category"), "Book index lookup resolves entries");

    // Consolidated lean_search: concordance source
    const callConc = await server.handleMessage({
        jsonrpc: "2.0",
        id: 7,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "functor", source: "concordance" },
        },
    });
    assert(callConc && callConc.result && callConc.result.content[0].text.length > 0, "Cross-ITP concordance resolves entries");

    // Consolidated lean_metrics: census
    const callCensus = await server.handleMessage({
        jsonrpc: "2.0",
        id: 8,
        method: "tools/call",
        params: {
            name: "lean_metrics",
            arguments: { action: "census", target: "src" },
        },
    });
    assert(callCensus && callCensus.result && !callCensus.result.isError, "Module census succeeds");

    // Consolidated lean_metrics: bigraph projection
    const leanRulesPath = path.resolve(__dirname, "../../rust-mmap-engine/lean_rules");
    const testTarget = fs.existsSync(leanRulesPath) ? leanRulesPath : "src";
    const callBigraph = await server.handleMessage({
        jsonrpc: "2.0",
        id: 81,
        method: "tools/call",
        params: {
            name: "lean_metrics",
            arguments: { action: "bigraph", target: testTarget, format: "json" },
        },
    });
    assert(callBigraph && callBigraph.result && !callBigraph.result.isError, "Bigraph projection succeeds");
    const bigraphData = JSON.parse(callBigraph.result.content[0].text);
    assert(bigraphData.place_graph && Array.isArray(bigraphData.place_graph.nodes), "Bigraph contains place_graph nodes");
    assert(bigraphData.link_graph && Array.isArray(bigraphData.link_graph.hyperedges), "Bigraph contains link_graph hyperedges");

    // Consolidated lean_metrics: axiom audit
    const callAxioms = await server.handleMessage({
        jsonrpc: "2.0",
        id: 82,
        method: "tools/call",
        params: {
            name: "lean_metrics",
            arguments: { action: "axiom_audit", target: testTarget, format: "json" },
        },
    });
    assert(callAxioms && callAxioms.result && !callAxioms.result.isError, "Axiom audit succeeds");
    const axiomData = JSON.parse(callAxioms.result.content[0].text);
    assert(axiomData.clean === true, "Axiom audit clean pass verified");
    assert(axiomData.custom_axioms.length === 0, "Zero custom axioms verified");
    assert(axiomData.sorries.length === 0, "Zero sorries verified");

    // Consolidated lean_ffi: sysroot flags
    const callFfi = await server.handleMessage({
        jsonrpc: "2.0",
        id: 9,
        method: "tools/call",
        params: {
            name: "lean_ffi",
            arguments: { action: "sysroot" },
        },
    });
    assert(callFfi && callFfi.result && callFfi.result.content[0].text.includes("Lean Sysroot"), "FFI sysroot query succeeds");

    // Legacy tool routing (backward-compatibility)
    const callLegacy = await server.handleMessage({
        jsonrpc: "2.0",
        id: 10,
        method: "tools/call",
        params: {
            name: "lean_ontology_search",
            arguments: { query: "liquid" },
        },
    });
    assert(callLegacy && callLegacy.result && callLegacy.result.content[0].text.includes("CONCEPT-CONDENSED-MATHEMATICS-LIQUID-VECTOR-SPACES"), "Legacy alias routing works");

    server.dispose();
    console.log("  - McpServer Dispatch (6 consolidated tools + Kuzu graph + legacy aliases): PASS");
}

// 5. LakeBuildGuard Concurrency Check
{
    const { LakeBuildGuard } = await import("../src/index.ts");
    const status = LakeBuildGuard.checkLock(repoRoot);
    assert(typeof status.isLocked === "boolean", "isLocked is a boolean");
    assert(typeof status.source === "string", "source is a string");
    console.log("  - LakeBuildGuard: PASS (isLocked=" + status.isLocked + ", source=" + status.source + ")");
}


// 6. SharedMemorySnapshotRing Lock-Free IPC
{
    const { SharedMemorySnapshotRing } = await import("../src/index.ts");
    const testShmPath = path.join(os.tmpdir(), `test_lean_shm_${process.pid}.shm`);
    const ring = SharedMemorySnapshotRing.create(testShmPath, 8, 4096);
    assert(ring !== null, "SharedMemorySnapshotRing created successfully");

    const seq = ring.writeSnapshot("/repo/Test.lean", 42, 10, "case intro\n|- True", 1, 1);
    assert.strictEqual(seq, 1n, "First write sequence is 1");

    const latest = ring.readLatest();
    assert(latest !== null, "Latest snapshot is readable");
    assert.strictEqual(latest.seq, 1n, "Snapshot sequence matches");
    assert.strictEqual(latest.filePath, "/repo/Test.lean", "Snapshot filePath matches");
    assert.strictEqual(latest.line, 42, "Snapshot line matches");
    assert.strictEqual(latest.col, 10, "Snapshot col matches");
    assert.strictEqual(latest.goalText, "case intro\n|- True", "Snapshot goalText matches");

    ring.dispose();
    console.log("  - SharedMemorySnapshotRing: PASS");
}

// 7. MultiPackageWorkspaceCoordinator & Global Build Lock Arbitration
{
    const { MultiPackageWorkspaceCoordinator, LakeBuildGuard } = await import("../src/index.ts");
    const testWs = fs.mkdtempSync(path.join(os.tmpdir(), "lean_ws_"));
    const pkgADir = path.join(testWs, "packages", "pkg-a");
    const pkgBDir = path.join(testWs, "packages", "pkg-b");
    fs.mkdirSync(pkgADir, { recursive: true });
    fs.mkdirSync(pkgBDir, { recursive: true });
    fs.writeFileSync(path.join(pkgADir, "lakefile.lean"), "-- pkg-a");
    fs.writeFileSync(path.join(pkgBDir, "lakefile.toml"), 'name = "pkg-b"');

    const coord = new MultiPackageWorkspaceCoordinator(testWs);
    const count = coord.getPackageCount();
    assert.strictEqual(count, 2, "Discovered exactly 2 mock Lean packages");

    const resolved = coord.resolvePackageForFile(path.join(pkgADir, "PkgA", "Main.lean"));
    assert(resolved !== null, "Resolved package for pkg-a file");
    assert.strictEqual(resolved.name, "pkg-a", "Package name matches pkg-a");

    // Test global build lock detection
    const testGlobalLock = "/dev/shm/lean_global_workspace.lock";
    const lockInfo = {
        pid: process.pid,
        packageName: "pkg-a",
        acquiredAt: Date.now(),
        ttlMs: 60000,
    };
    fs.writeFileSync(testGlobalLock, JSON.stringify(lockInfo));

    const status = LakeBuildGuard.checkLock(testWs);
    assert.strictEqual(status.isLocked, true, "Global workspace lock detected");
    assert.strictEqual(status.source, "global_workspace_lock", "Source is global_workspace_lock");
    assert(status.detail && status.detail.includes("pkg-a"), "Detail mentions active package");

    try { fs.unlinkSync(testGlobalLock); } catch {}
    fs.rmSync(testWs, { recursive: true, force: true });
    console.log("  - MultiPackageWorkspaceCoordinator: PASS (packages=" + count + ")");
}

console.log("=== All lean4-lsp-mcp Tests Passed ===");
