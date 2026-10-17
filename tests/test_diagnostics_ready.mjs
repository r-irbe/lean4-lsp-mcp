// tests/test_diagnostics_ready.mjs
// Regression tests for lean_diagnostics readiness (FileWorkerManager.getDiagnostics).
// Strict 7-bit ASCII only (INV-001).
//
// Regression origin: Lean publishes an EMPTY textDocument/publishDiagnostics when
// analysis STARTS. getDiagnostics latched that first snapshot, so the first call
// after didOpen answered "0 findings" for a file with 4 elaboration errors - the
// second call (same session) returned them. A false "clean" is the worst possible
// answer for a proof gate, so the verb now waits for $/lean/fileProgress with no
// pending regions (the observed completion signal) and refuses to call an
// unfinished analysis clean.

import assert from "node:assert";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { EventEmitter } from "node:events";
import { PassThrough } from "node:stream";
import { pathToFileURL } from "node:url";
import { FileWorkerManager } from "../src/index.ts";

console.log("=== Testing lean_diagnostics readiness ===");

const root = fs.mkdtempSync(path.join(os.tmpdir(), "lean-diag-"));
fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "diag"\n');

function makeManager() {
  const manager = new FileWorkerManager(root);
  const child = new EventEmitter();
  child.stdin = new PassThrough();
  child.stdout = new PassThrough();
  child.pid = 1;
  child.exitCode = null;
  child.kill = () => { child.exitCode = 0; child.emit("exit", 0); };
  const session = {
    child,
    leanRoot: root,
    nextId: 1,
    pendingRequests: new Map(),
    openFiles: new Map(),
    diagnostics: new Map(),
    progress: new Map(),
    buffer: Buffer.alloc(0),
    lastActiveMs: Date.now(),
  };
  manager["sessions"].set(root, session);
  const send = (msg) => {
    const body = JSON.stringify(msg);
    child.stdout.write(Buffer.from(`Content-Length: ${Buffer.byteLength(body, "utf-8")}\r\n\r\n${body}`));
  };
  return { manager, session, send };
}

function makeFile(name, text) {
  const p = path.join(root, name);
  fs.writeFileSync(p, text);
  return p;
}

const uriOf = (p) => pathToFileURL(p).href;
const diags = (n) =>
  Array.from({ length: n }, (_, i) => ({
    range: { start: { line: i + 1, character: 64 }, end: { line: i + 1, character: 70 } },
    severity: 1,
    message: "unknown tactic",
  }));

// 1. Errors published after an empty "analysis started" snapshot are reported.
{
  const { manager, session, send } = makeManager();
  const file = makeFile("Broken.lean", "theorem t : 1 = 2 := by linarith\n");

  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "textDocument/publishDiagnostics", params: { uri: uriOf(file), version: 1, diagnostics: [] } });
  }, 20);
  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "$/lean/fileProgress", params: { textDocument: { uri: uriOf(file), version: 1 }, processing: [{ kind: 1, range: { start: { line: 0, character: 0 }, end: { line: 1, character: 0 } } }] } });
  }, 40);
  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "textDocument/publishDiagnostics", params: { uri: uriOf(file), version: 1, diagnostics: diags(2) } });
  }, 60);
  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "$/lean/fileProgress", params: { textDocument: { uri: uriOf(file), version: 1 }, processing: [] } });
  }, 80);

  // Drive the session's frame handler exactly as ensureSession's stdout listener does.
  session.child.stdout.on("data", (chunk) => {
    session.buffer = Buffer.concat([session.buffer, chunk]);
    while (true) {
      const idx = session.buffer.indexOf("\r\n\r\n");
      if (idx === -1) break;
      const len = parseInt(/Content-Length:\s*(\d+)/i.exec(session.buffer.subarray(0, idx).toString("utf-8"))[1], 10);
      if (session.buffer.length < idx + 4 + len) break;
      const body = session.buffer.subarray(idx + 4, idx + 4 + len).toString("utf-8");
      session.buffer = session.buffer.subarray(idx + 4 + len);
      manager.handleServerMessage(session, JSON.parse(body));
    }
  });

  const report = await manager.getDiagnostics(file, 3000);
  assert.ok(!report.includes("No diagnostics"), `empty snapshot must not be reported as clean, got: ${report}`);
  assert.ok(report.includes("2 diagnostic(s)"), `error count reported, got: ${report}`);
  assert.ok(report.includes("L2:65 error: unknown tactic"), `error position + message reported, got: ${report}`);
  manager.dispose();
  console.log("  - errors after empty snapshot: PASS");
}

// 2. An unfinished analysis is never reported as clean.
{
  const { manager, send } = makeManager();
  const file = makeFile("Slow.lean", "theorem t : 1 = 1 := by rfl\n");
  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "textDocument/publishDiagnostics", params: { uri: uriOf(file), version: 1, diagnostics: [] } });
  }, 20);
  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "$/lean/fileProgress", params: { textDocument: { uri: uriOf(file), version: 1 }, processing: [{ kind: 1, range: { start: { line: 0, character: 0 }, end: { line: 1, character: 0 } } }] } });
  }, 40);

  const session = manager["sessions"].get(root);
  session.child.stdout.on("data", (chunk) => {
    session.buffer = Buffer.concat([session.buffer, chunk]);
    while (true) {
      const idx = session.buffer.indexOf("\r\n\r\n");
      if (idx === -1) break;
      const len = parseInt(/Content-Length:\s*(\d+)/i.exec(session.buffer.subarray(0, idx).toString("utf-8"))[1], 10);
      if (session.buffer.length < idx + 4 + len) break;
      const body = session.buffer.subarray(idx + 4, idx + 4 + len).toString("utf-8");
      session.buffer = session.buffer.subarray(idx + 4 + len);
      manager.handleServerMessage(session, JSON.parse(body));
    }
  });

  const report = await manager.getDiagnostics(file, 400);
  assert.ok(report.startsWith("analysis_incomplete:"), `unfinished analysis is labelled, got: ${report}`);
  assert.ok(report.includes("NOT a clean result"), `explicit non-clean warning, got: ${report}`);
  manager.dispose();
  console.log("  - unfinished analysis: PASS");
}

// 3. A completed analysis with zero findings is the only "clean" answer.
{
  const { manager, send } = makeManager();
  const file = makeFile("Clean.lean", "theorem t : 1 = 1 := by rfl\n");
  setTimeout(() => {
    send({ jsonrpc: "2.0", method: "textDocument/publishDiagnostics", params: { uri: uriOf(file), version: 1, diagnostics: [] } });
    send({ jsonrpc: "2.0", method: "$/lean/fileProgress", params: { textDocument: { uri: uriOf(file), version: 1 }, processing: [] } });
  }, 20);

  const session = manager["sessions"].get(root);
  session.child.stdout.on("data", (chunk) => {
    session.buffer = Buffer.concat([session.buffer, chunk]);
    while (true) {
      const idx = session.buffer.indexOf("\r\n\r\n");
      if (idx === -1) break;
      const len = parseInt(/Content-Length:\s*(\d+)/i.exec(session.buffer.subarray(0, idx).toString("utf-8"))[1], 10);
      if (session.buffer.length < idx + 4 + len) break;
      const body = session.buffer.subarray(idx + 4, idx + 4 + len).toString("utf-8");
      session.buffer = session.buffer.subarray(idx + 4 + len);
      manager.handleServerMessage(session, JSON.parse(body));
    }
  });

  const report = await manager.getDiagnostics(file, 2000);
  assert.ok(report.includes("analysis completed, 0 findings"), `clean answer names the completion, got: ${report}`);
  manager.dispose();
  console.log("  - completed clean analysis: PASS");
}

fs.rmSync(root, { recursive: true, force: true });
console.log("=== lean_diagnostics readiness suite: ALL PASS ===");
