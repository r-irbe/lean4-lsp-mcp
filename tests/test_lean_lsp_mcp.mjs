// tools/lean_lsp_mcp/tests/test_lean_lsp_mcp.mjs
// Unit and integration test suite for lean-lsp-mcp standalone module
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert";
import { spawn } from "node:child_process";
import * as path from "node:path";
import * as os from "node:os";
import { fileURLToPath } from "node:url";
import {
    FileWorkerManager,
    Lean4IleanIndex,
    LeanSysrootBridge,
    formatGoalAsMarkdown,
    McpServer,
    TOOL_DEFINITIONS,
} from "../src/index.ts";

import * as fs from "node:fs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
let repoRoot = process.env.LEAN_PROJECT_ROOT;
if (!repoRoot) {
    let curr = pkgRoot;
    while (curr !== path.dirname(curr)) {
        if (fs.existsSync(path.join(curr, "packages")) && fs.existsSync(path.join(curr, "docs", "easci", "lean"))) {
            repoRoot = curr;
            break;
        }
        curr = path.dirname(curr);
    }
}
if (!repoRoot) repoRoot = path.resolve(pkgRoot, "../tacit-mui");
if (!fs.existsSync(repoRoot)) repoRoot = pkgRoot;

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
    assert.strictEqual(listRes.result.tools.length, 13, "Exposes 13 tools (5 core + lean_filtered_goal + 2 old + 5 search/discovery: loogle/local/leansearch/arxiv/reservoir/datasets)");

    const toolNames = listRes.result.tools.map(t => t.name);
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

    server.dispose();
    console.log("  - McpServer Dispatch (all 13 tools): PASS");
}

// 5. LakeBuildGuard Concurrency Check
{
    const { LakeBuildGuard } = await import("../src/index.ts");
    const status = LakeBuildGuard.checkLock(repoRoot);
    assert(typeof status.isLocked === "boolean", "isLocked is a boolean");
    assert(typeof status.source === "string", "source is a string");
    console.log("  - LakeBuildGuard: PASS (isLocked=" + status.isLocked + ", source=" + status.source + ")");
}

// 6. FileWorkerManager stdout session parsing and error handling
{
    const manager = new FileWorkerManager(repoRoot);

    const helperMakeChunk = (body) => {
        const msg = typeof body === "string" ? body : JSON.stringify(body);
        const header = `Content-Length: ${Buffer.byteLength(msg, "utf-8")}\r\n\r\n`;
        return Buffer.from(header + msg, "utf-8");
    };

    // Sub-test 1: Successful result resolution
    {
        const pendingRequests = new Map();
        let resolvedValue = null;
        pendingRequests.set(1, {
            resolve: (val) => { resolvedValue = val; },
            reject: (err) => { throw err; },
        });

        const mockSession = {
            buffer: Buffer.alloc(0),
            pendingRequests,
        };

        const chunk = helperMakeChunk({ jsonrpc: "2.0", id: 1, result: { rendered: "Goal state" } });
        manager.handleStdoutData(mockSession, chunk);

        assert.deepStrictEqual(resolvedValue, { rendered: "Goal state" }, "Resolves parsed result");
        assert.strictEqual(pendingRequests.has(1), false, "Pending request deleted after resolution");
    }

    // Sub-test 2: Error response with error.message
    {
        const pendingRequests = new Map();
        let rejectedError = null;
        pendingRequests.set(2, {
            resolve: () => { assert.fail("Should not resolve"); },
            reject: (err) => { rejectedError = err; },
        });

        const mockSession = {
            buffer: Buffer.alloc(0),
            pendingRequests,
        };

        const chunk = helperMakeChunk({
            jsonrpc: "2.0",
            id: 2,
            error: { code: -32603, message: "Server error occurred" },
        });
        manager.handleStdoutData(mockSession, chunk);

        assert(rejectedError instanceof Error, "Rejects with Error instance");
        assert.strictEqual(rejectedError.message, "Server error occurred", "Error message contains error.message");
        assert.strictEqual(pendingRequests.has(2), false, "Pending request deleted after rejection");
    }

    // Sub-test 3: Error response without error.message (fallback to JSON.stringify)
    {
        const pendingRequests = new Map();
        let rejectedError = null;
        pendingRequests.set(3, {
            resolve: () => { assert.fail("Should not resolve"); },
            reject: (err) => { rejectedError = err; },
        });

        const mockSession = {
            buffer: Buffer.alloc(0),
            pendingRequests,
        };

        const chunk = helperMakeChunk({
            jsonrpc: "2.0",
            id: 3,
            error: { code: -32601 },
        });
        manager.handleStdoutData(mockSession, chunk);

        assert(rejectedError instanceof Error, "Rejects with Error instance");
        assert.strictEqual(rejectedError.message, '{"code":-32601}', "Error message falls back to JSON.stringify(error)");
        assert.strictEqual(pendingRequests.has(3), false, "Pending request deleted after rejection");
    }

    // Sub-test 4: Malformed/transient JSON parse error in body
    {
        const pendingRequests = new Map();
        let called = false;
        pendingRequests.set(4, {
            resolve: () => { called = true; },
            reject: () => { called = true; },
        });

        const mockSession = {
            buffer: Buffer.alloc(0),
            pendingRequests,
        };

        const malformedChunk = helperMakeChunk("{ invalid json payload");
        assert.doesNotThrow(() => {
            manager.handleStdoutData(mockSession, malformedChunk);
        }, "Does not throw on invalid JSON");

        assert.strictEqual(called, false, "Handler neither resolved nor rejected on JSON parse error");
        assert.strictEqual(pendingRequests.has(4), true, "Pending request remains intact during transient parse failure");
    }

    // Sub-test 5: Fragmented chunks across multiple stdout events
    {
        const pendingRequests = new Map();
        let resolvedValue = null;
        pendingRequests.set(5, {
            resolve: (val) => { resolvedValue = val; },
            reject: (err) => { throw err; },
        });

        const mockSession = {
            buffer: Buffer.alloc(0),
            pendingRequests,
        };

        const fullBuffer = helperMakeChunk({ jsonrpc: "2.0", id: 5, result: "fragmented-success" });
        const part1 = fullBuffer.subarray(0, 15);
        const part2 = fullBuffer.subarray(15);

        manager.handleStdoutData(mockSession, part1);
        assert.strictEqual(resolvedValue, null, "Not resolved after partial chunk");
        assert.strictEqual(pendingRequests.has(5), true, "Pending request remains until full message received");

        manager.handleStdoutData(mockSession, part2);
        assert.strictEqual(resolvedValue, "fragmented-success", "Resolves once full chunk is buffered");
        assert.strictEqual(pendingRequests.has(5), false, "Pending request deleted after full message processed");
    }

    manager.dispose();
    console.log("  - FileWorkerManager Stdout Handler & Error Tests: PASS");
}

console.log("=== All lean4-lsp-mcp Tests Passed ===");
