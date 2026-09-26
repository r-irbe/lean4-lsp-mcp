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
    assert.strictEqual(toolNames.length, 16, "Exposes exactly 16 tools");

    assert(toolNames.includes("lean_goal"), "Includes lean_goal");
    assert(toolNames.includes("lean_term_goal"), "Includes lean_term_goal");
    assert(toolNames.includes("lean_lookup_symbol"), "Includes lean_lookup_symbol");
    assert(toolNames.includes("lean_module_hierarchy"), "Includes lean_module_hierarchy");
    assert(toolNames.includes("lean_c_ffi_inspect"), "Includes lean_c_ffi_inspect");
    assert(toolNames.includes("lean_filtered_goal"), "Includes lean_filtered_goal");
    assert(toolNames.includes("lean_run_code"), "Includes lean_run_code");
    assert(toolNames.includes("lean_loogle_search"), "Includes lean_loogle_search");
    assert(toolNames.includes("lean_local_search"), "Includes lean_local_search");
    assert(toolNames.includes("lean_search"), "Includes lean_search");
    assert(toolNames.includes("lean_arxiv_search"), "Includes lean_arxiv_search");
    assert(toolNames.includes("lean_reservoir_search"), "Includes lean_reservoir_search");
    assert(toolNames.includes("lean_dataset_search"), "Includes lean_dataset_search");
    assert(toolNames.includes("lean_ontology_search"), "Includes lean_ontology_search");
    assert(toolNames.includes("lean_book_index_lookup"), "Includes lean_book_index_lookup");
    assert(toolNames.includes("lean_cross_itp_concordance"), "Includes lean_cross_itp_concordance");

    const callOnto = await server.handleMessage({
        jsonrpc: "2.0",
        id: 3,
        method: "tools/call",
        params: {
            name: "lean_ontology_search",
            arguments: { query: "liquid" },
        },
    });
    assert(callOnto && callOnto.result && callOnto.result.content[0].text.includes("CONCEPT-CONDENSED-MATHEMATICS-LIQUID-VECTOR-SPACES"), "Ontology search resolves concept");

    const callBook = await server.handleMessage({
        jsonrpc: "2.0",
        id: 4,
        method: "tools/call",
        params: {
            name: "lean_book_index_lookup",
            arguments: { term: "category" },
        },
    });
    assert(callBook && callBook.result && callBook.result.content[0].text.includes("category"), "Book index lookup resolves entries");

    const callConc = await server.handleMessage({
        jsonrpc: "2.0",
        id: 5,
        method: "tools/call",
        params: {
            name: "lean_cross_itp_concordance",
            arguments: { concept: "functor" },
        },
    });
    assert(callConc && callConc.result && callConc.result.content[0].text.length > 0, "Cross-ITP concordance resolves entries");

    server.dispose();
    console.log("  - McpServer Dispatch (all 16 tools + ontology + book + concordance): PASS");
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
