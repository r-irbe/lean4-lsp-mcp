// tools/check-wasm-size.mjs
// Authoritative raw WASM binary size gate for data/lean_analyzer.wasm.
// Scoped Unicode policy (INV-001; typographic-free by default).

import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";

export const MAX_WASM_BYTES = 131_072;

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
export const DEFAULT_WASM_PATH = path.resolve(__dirname, "../data/lean_analyzer.wasm");

export function checkWasmSize(wasmPath = DEFAULT_WASM_PATH, ceilingBytes = MAX_WASM_BYTES) {
  const resolved = path.resolve(wasmPath);
  let lstat;
  try {
    lstat = fs.lstatSync(resolved);
  } catch {
    return {
      ok: false,
      reason: "missing",
      path: resolved,
      ceilingBytes,
      detail: "WASM artifact path does not exist",
    };
  }

  if (lstat.isSymbolicLink()) {
    return {
      ok: false,
      reason: "symlink",
      path: resolved,
      ceilingBytes,
      detail: "WASM artifact must be a regular file, not a symlink",
    };
  }

  if (!lstat.isFile()) {
    return {
      ok: false,
      reason: "non-regular",
      path: resolved,
      ceilingBytes,
      detail: "WASM artifact is not a regular file",
    };
  }

  if ((lstat.mode & 0o444) === 0) {
    return {
      ok: false,
      reason: "unreadable",
      path: resolved,
      ceilingBytes,
      detail: "WASM artifact has no read permission bits",
    };
  }

  let data;
  try {
    const fd = fs.openSync(resolved, fs.constants.O_RDONLY | (fs.constants.O_NOFOLLOW ?? 0));
    try {
      data = fs.readFileSync(fd);
    } finally {
      fs.closeSync(fd);
    }
  } catch (err) {
    return {
      ok: false,
      reason: "unreadable",
      path: resolved,
      ceilingBytes,
      detail: `Failed to read WASM artifact: ${err instanceof Error ? err.message : String(err)}`,
    };
  }

  const bytes = data.length;
  const sha256 = createHash("sha256").update(data).digest("hex");

  if (bytes <= 0) {
    return {
      ok: false,
      reason: "empty",
      path: resolved,
      bytes,
      sizeBytes: bytes,
      ceilingBytes,
      sha256,
      detail: "WASM artifact is 0 bytes",
    };
  }

  if (bytes > ceilingBytes) {
    return {
      ok: false,
      reason: "exceeds-ceiling",
      path: resolved,
      bytes,
      sizeBytes: bytes,
      ceilingBytes,
      overByBytes: bytes - ceilingBytes,
      sha256,
      detail: `WASM artifact is ${bytes} bytes, exceeding fixed ceiling ${ceilingBytes} bytes`,
    };
  }

  return {
    ok: true,
    reason: "within-budget",
    path: resolved,
    bytes,
    sizeBytes: bytes,
    ceilingBytes,
    headroomBytes: ceilingBytes - bytes,
    sha256,
  };
}

if (process.argv[1] && path.resolve(process.argv[1]) === __filename) {
  const args = process.argv.slice(2);
  let targetPath = DEFAULT_WASM_PATH;
  if (args.length === 2 && args[0] === "--wasm") {
    targetPath = args[1];
  } else if (args.length !== 0) {
    console.error("Usage: node tools/check-wasm-size.mjs [--wasm <path>]");
    process.exitCode = 2;
    targetPath = "";
  }
  if (targetPath) {
    const result = checkWasmSize(targetPath);
    console.log(JSON.stringify(result, null, 2));
    process.exitCode = result.ok ? 0 : 1;
  }
}
