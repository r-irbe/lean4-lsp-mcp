// tests/test_file_worker_manager.mjs
// Unit and integration test suite for FileWorkerManager
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert";
import * as fs from "node:fs";
import * as path from "node:path";
import { EventEmitter } from "node:events";
import { PassThrough } from "node:stream";
import { fileURLToPath } from "node:url";
import {
    FileWorkerManager,
    LakeBuildGuard,
} from "../src/index.ts";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
const repoRoot = process.env.LEAN_PROJECT_ROOT || pkgRoot;

console.log("=== Testing FileWorkerManager Suite ===");

// Helper to create a fake ChildProcess double
function createMockChildProcess() {
    const child = new EventEmitter();
    child.stdin = new PassThrough();
    child.stdout = new PassThrough();
    child.pid = 99999;
    child.exitCode = null;
    child.kill = function (signal) {
        child.exitCode = 0;
        child.emit("exit", 0, signal || "SIGTERM");
    };
    return child;
}

// 1. findLeanRoot
{
    const manager = new FileWorkerManager(repoRoot);

    // 1.1 Non-existent path or path with no lakefile returns projectRoot
    const root1 = manager.findLeanRoot(path.join(repoRoot, "some/nonexistent/file.lean"));
    assert.strictEqual(root1, repoRoot, "Fallback to projectRoot when no lakefile present");

    // 1.2 Path inside a directory containing lakefile.lean returns that directory
    const tempDir = fs.mkdtempSync(path.join(repoRoot, "temp_test_lean_root_"));
    const nestedDir = path.join(tempDir, "nested", "sub");
    fs.mkdirSync(nestedDir, { recursive: true });
    const lakefile = path.join(tempDir, "lakefile.lean");
    fs.writeFileSync(lakefile, "-- test lakefile");

    const targetFile = path.join(nestedDir, "Main.lean");
    const foundRoot = manager.findLeanRoot(targetFile);
    assert.strictEqual(foundRoot, tempDir, "findLeanRoot locates directory with lakefile.lean");

    // Cleanup temp dir
    fs.rmSync(tempDir, { recursive: true, force: true });
    manager.dispose();
    console.log("  - findLeanRoot: PASS");
}

// 2. getProcessRssKb
{
    const manager = new FileWorkerManager(repoRoot);

    // 2.1 Missing PID returns 0
    assert.strictEqual(manager.getProcessRssKb(undefined), 0, "Undefined PID returns 0");
    assert.strictEqual(manager.getProcessRssKb(0), 0, "PID 0 returns 0");

    // 2.2 Invalid PID returns 0
    assert.strictEqual(manager.getProcessRssKb(99999999), 0, "Non-existent PID returns 0");

    // 2.3 Current PID test (if /proc available on Linux)
    const rss = manager.getProcessRssKb(process.pid);
    assert(typeof rss === "number", "Returns a number for process RSS");

    manager.dispose();
    console.log("  - getProcessRssKb: PASS");
}

// 3. reapIdleAndHeavyWorkers
{
    // 3.1 Idle file cleanup
    {
        const manager = new FileWorkerManager(repoRoot);
        const child = createMockChildProcess();

        let writtenData = "";
        child.stdin.on("data", (chunk) => {
            writtenData += chunk.toString("utf-8");
        });

        const mockSession = {
            child,
            leanRoot: repoRoot,
            nextId: 1,
            pendingRequests: new Map(),
            openFiles: new Map(),
            buffer: Buffer.alloc(0),
            lastActiveMs: Date.now(),
        };

        const idleFilePath = path.join(repoRoot, "IdleFile.lean");
        const activeFilePath = path.join(repoRoot, "ActiveFile.lean");
        const now = Date.now();

        mockSession.openFiles.set(idleFilePath, {
            uri: "file://" + idleFilePath,
            absPath: idleFilePath,
            version: 1,
            mtimeMs: now - 100000,
            lastAccessedMs: now - 70000, // > 60000 ms idle
        });

        mockSession.openFiles.set(activeFilePath, {
            uri: "file://" + activeFilePath,
            absPath: activeFilePath,
            version: 1,
            mtimeMs: now,
            lastAccessedMs: now - 5000, // active
        });

        manager["sessions"].set(repoRoot, mockSession);

        manager.reapIdleAndHeavyWorkers();

        assert(!mockSession.openFiles.has(idleFilePath), "Idle file removed from openFiles");
        assert(mockSession.openFiles.has(activeFilePath), "Active file retained in openFiles");
        assert(writtenData.includes("textDocument/didClose"), "didClose notification sent for idle file");
        assert(writtenData.includes(idleFilePath), "didClose notification target is idle file");

        manager.dispose();
    }

    // 3.2 Idle session disposal
    {
        const manager = new FileWorkerManager(repoRoot);
        const child = createMockChildProcess();

        const mockSession = {
            child,
            leanRoot: repoRoot,
            nextId: 1,
            pendingRequests: new Map(),
            openFiles: new Map(), // No open files
            buffer: Buffer.alloc(0),
            lastActiveMs: Date.now() - 130000, // > 120000 ms idle
        };

        manager["sessions"].set(repoRoot, mockSession);
        assert.strictEqual(manager["sessions"].size, 1);

        manager.reapIdleAndHeavyWorkers();

        assert.strictEqual(manager["sessions"].size, 0, "Idle session with no open files is disposed");

        manager.dispose();
    }

    // 3.3 Heavy worker memory ceiling disposal
    {
        const manager = new FileWorkerManager(repoRoot);
        const child = createMockChildProcess();

        const mockSession = {
            child,
            leanRoot: repoRoot,
            nextId: 1,
            pendingRequests: new Map(),
            openFiles: new Map(),
            buffer: Buffer.alloc(0),
            lastActiveMs: Date.now(),
        };

        manager["sessions"].set(repoRoot, mockSession);

        // Override getProcessRssKb temporarily to simulate memory ceiling exceedance (> 2 * 1048576 KB)
        const origGetRss = manager.getProcessRssKb;
        manager.getProcessRssKb = () => 3000000;

        manager.reapIdleAndHeavyWorkers();

        assert.strictEqual(manager["sessions"].size, 0, "Heavy worker exceeding memory ceiling is disposed");

        manager.getProcessRssKb = origGetRss;
        manager.dispose();
    }

    console.log("  - reapIdleAndHeavyWorkers: PASS");
}

// 4. LSP Message Parsing and Framing
{
    const manager = new FileWorkerManager(repoRoot);
    const child = createMockChildProcess();

    const mockSession = {
        child,
        leanRoot: repoRoot,
        nextId: 1,
        pendingRequests: new Map(),
        openFiles: new Map(),
        buffer: Buffer.alloc(0),
        lastActiveMs: Date.now(),
    };

    // Attach stdout listener logic as done in ensureSession
    child.stdout.on("data", (chunk) => {
        mockSession.buffer = Buffer.concat([mockSession.buffer, chunk]);
        while (true) {
            const idx = mockSession.buffer.indexOf("\r\n\r\n");
            if (idx === -1) break;
            const header = mockSession.buffer.subarray(0, idx).toString("utf-8");
            const match = header.match(/Content-Length:\s*(\d+)/i);
            if (!match) {
                mockSession.buffer = mockSession.buffer.subarray(idx + 4);
                continue;
            }
            const len = parseInt(match[1], 10);
            if (mockSession.buffer.length < idx + 4 + len) break;
            const body = mockSession.buffer.subarray(idx + 4, idx + 4 + len).toString("utf-8");
            mockSession.buffer = mockSession.buffer.subarray(idx + 4 + len);
            try {
                const parsed = JSON.parse(body);
                if (parsed.id !== undefined && mockSession.pendingRequests.has(parsed.id)) {
                    const handler = mockSession.pendingRequests.get(parsed.id);
                    mockSession.pendingRequests.delete(parsed.id);
                    if (parsed.error) {
                        handler.reject(new Error(parsed.error.message || JSON.stringify(parsed.error)));
                    } else {
                        handler.resolve(parsed.result);
                    }
                }
            } catch {
                // Ignore parsing errors
            }
        }
    });

    manager["sessions"].set(repoRoot, mockSession);

    // Test sendRequest resolve
    const reqPromise = manager["sendRequest"](mockSession, "$/lean/plainGoal", { textDocument: { uri: "file://test.lean" } });

    // Simulate child sending LSP response
    const responseObj = { jsonrpc: "2.0", id: 1, result: { rendered: "goals: 1\n|- True" } };
    const responseJson = JSON.stringify(responseObj);
    const responseHeader = `Content-Length: ${Buffer.byteLength(responseJson, "utf-8")}\r\n\r\n`;

    child.stdout.write(Buffer.from(responseHeader + responseJson));

    const res = await reqPromise;
    assert.deepStrictEqual(res, { rendered: "goals: 1\n|- True" }, "LSP request resolves with parsed result");

    // Test sendRequest error reject
    const errPromise = manager["sendRequest"](mockSession, "$/lean/plainGoal", { textDocument: { uri: "file://test.lean" } });
    const errResponseObj = { jsonrpc: "2.0", id: 2, error: { code: -32603, message: "Internal error" } };
    const errResponseJson = JSON.stringify(errResponseObj);
    const errResponseHeader = `Content-Length: ${Buffer.byteLength(errResponseJson, "utf-8")}\r\n\r\n`;

    child.stdout.write(Buffer.from(errResponseHeader + errResponseJson));

    await assert.rejects(errPromise, /Internal error/, "LSP request rejects on JSON-RPC error");

    manager.dispose();
    console.log("  - LSP Message Framing & Request Handling: PASS");
}

// 5. Build Lock Fallback & Concurrency Controls
{
    const manager = new FileWorkerManager(repoRoot);

    // 5.1 Non-existent file returns error string
    const goalNonExistent = await manager.getGoal("non_existent_file_12345.lean", 1, 1);
    assert(goalNonExistent.startsWith("File not found:"), "Non-existent file returns File not found");

    const termGoalNonExistent = await manager.getTermGoal("non_existent_file_12345.lean", 1, 1);
    assert(termGoalNonExistent.startsWith("File not found:"), "Non-existent term goal returns File not found");

    // 5.2 Build Lock Fallback
    const origInspect = LakeBuildGuard.inspectBuildActivity;
    LakeBuildGuard.inspectBuildActivity = () => ({
        isLocked: true,
        source: "lockfile",
        detail: "Simulated lock for test",
    });

    // Create a real file for testing
    const tempFile = path.join(repoRoot, "TempLockTest.lean");
    fs.writeFileSync(tempFile, "theorem test : True := by trivial");

    try {
        const fallbackGoal = await manager.getGoal(tempFile, 1, 1);
        assert(fallbackGoal.includes("[Zero-Build Concurrency Gate]"), "getGoal returns Zero-Build fallback when build is locked");
        assert(fallbackGoal.includes("Simulated lock for test"), "Fallback includes detail");

        const fallbackTermGoal = await manager.getTermGoal(tempFile, 1, 1);
        assert(fallbackTermGoal.includes("[Zero-Build Concurrency Gate]"), "getTermGoal returns Zero-Build fallback when build is locked");
    } finally {
        LakeBuildGuard.inspectBuildActivity = origInspect;
        if (fs.existsSync(tempFile)) fs.unlinkSync(tempFile);
    }

    manager.dispose();
    console.log("  - Build Lock Fallback & Concurrency: PASS");
}

// 6. Dispose & Resource Cleanup
{
    const manager = new FileWorkerManager(repoRoot);
    const child1 = createMockChildProcess();
    const child2 = createMockChildProcess();

    manager["sessions"].set("/root1", {
        child: child1,
        leanRoot: "/root1",
        nextId: 1,
        pendingRequests: new Map(),
        openFiles: new Map(),
        buffer: Buffer.alloc(0),
        lastActiveMs: Date.now(),
    });

    manager["sessions"].set("/root2", {
        child: child2,
        leanRoot: "/root2",
        nextId: 1,
        pendingRequests: new Map(),
        openFiles: new Map(),
        buffer: Buffer.alloc(0),
        lastActiveMs: Date.now(),
    });

    assert.strictEqual(manager["sessions"].size, 2);
    assert.notStrictEqual(manager["reaperTimer"], null);

    manager.dispose();

    assert.strictEqual(manager["sessions"].size, 0, "Sessions map emptied after dispose()");
    assert.strictEqual(manager["reaperTimer"], null, "Reaper timer cleared after dispose()");
    assert.strictEqual(child1.exitCode, 0, "Child process 1 killed");
    assert.strictEqual(child2.exitCode, 0, "Child process 2 killed");

    console.log("  - Dispose & Resource Cleanup: PASS");
}

console.log("=== All FileWorkerManager Tests Passed ===");
