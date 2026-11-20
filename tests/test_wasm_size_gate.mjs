// tests/test_wasm_size_gate.mjs
// Boundary and negative tests for tools/check-wasm-size.mjs (raw ceiling 163840 bytes).
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { checkWasmSize, MAX_WASM_BYTES } from "../tools/check-wasm-size.mjs";

test("live data/lean_analyzer.wasm passes the 163840-byte ceiling gate", () => {
  assert.equal(MAX_WASM_BYTES, 163840);
  const res = checkWasmSize();
  assert.equal(res.ok, true, `Expected live WASM to pass size gate: ${JSON.stringify(res)}`);
  assert.equal(res.reason, "within-budget");
  assert.ok(res.bytes > 0 && res.bytes <= 163840);
  assert.match(res.sha256, /^[0-9a-f]{64}$/);
});

test("boundary and failure modes: missing, empty (0 B), symlink, unreadable, 163840 B PASS, 163841 B FAIL", () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "wasm-size-gate-"));
  try {
    // 1. Missing file -> FAIL
    const missingPath = path.join(tmpDir, "missing.wasm");
    const rMissing = checkWasmSize(missingPath);
    assert.equal(rMissing.ok, false);
    assert.equal(rMissing.reason, "missing");

    // 2. Empty 0-byte file -> FAIL
    const emptyPath = path.join(tmpDir, "empty.wasm");
    fs.writeFileSync(emptyPath, Buffer.alloc(0));
    const rEmpty = checkWasmSize(emptyPath);
    assert.equal(rEmpty.ok, false);
    assert.equal(rEmpty.reason, "empty");

    // 3. Exact boundary 163840 bytes -> PASS
    const exactCapPath = path.join(tmpDir, "cap_163840.wasm");
    fs.writeFileSync(exactCapPath, Buffer.alloc(163840, 0x61));
    const rExact = checkWasmSize(exactCapPath);
    assert.equal(rExact.ok, true);
    assert.equal(rExact.bytes, 163840);
    assert.equal(rExact.headroomBytes, 0);
    assert.equal(rExact.reason, "within-budget");

    // 4. 1 byte over ceiling (163841 bytes) -> FAIL
    const overCapPath = path.join(tmpDir, "over_163841.wasm");
    fs.writeFileSync(overCapPath, Buffer.alloc(163841, 0x61));
    const rOver = checkWasmSize(overCapPath);
    assert.equal(rOver.ok, false);
    assert.equal(rOver.bytes, 163841);
    assert.equal(rOver.reason, "exceeds-ceiling");

    // 5. Symlink -> FAIL
    const symlinkPath = path.join(tmpDir, "symlink.wasm");
    fs.symlinkSync(exactCapPath, symlinkPath);
    const rSymlink = checkWasmSize(symlinkPath);
    assert.equal(rSymlink.ok, false);
    assert.equal(rSymlink.reason, "symlink");

    // 6. Unreadable file -> FAIL (when not running as root)
    if (typeof process.getuid === "function" && process.getuid() !== 0) {
      const unreadablePath = path.join(tmpDir, "unreadable.wasm");
      fs.writeFileSync(unreadablePath, Buffer.alloc(16, 0x01), { mode: 0o000 });
      try {
        const rUnreadable = checkWasmSize(unreadablePath);
        assert.equal(rUnreadable.ok, false);
        assert.equal(rUnreadable.reason, "unreadable");
      } finally {
        fs.chmodSync(unreadablePath, 0o600);
      }
    }
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});
