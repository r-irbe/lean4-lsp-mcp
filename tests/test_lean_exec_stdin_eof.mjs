import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { McpServer } from "../src/index.ts";

const packageRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const projectRoot = fs.mkdtempSync(path.join(os.tmpdir(), "lean-exec-stdin-eof-"));
try {
  fs.writeFileSync(path.join(projectRoot, "lakefile.toml"), 'name = "stdinEofProbe"\n');
  const sourceToolchain = path.join(packageRoot, "lean-toolchain");
  if (fs.existsSync(sourceToolchain)) {
    fs.copyFileSync(sourceToolchain, path.join(projectRoot, "lean-toolchain"));
  } else {
    fs.writeFileSync(path.join(projectRoot, "lean-toolchain"), "leanprover/lean4:v4.33.1\n");
  }
  const server = new McpServer(projectRoot);
  const result = await server.executeTool("lean_run_code", {
    code: "#check Nat\n",
    timeoutMs: 5000,
  });
  assert.match(String(result), /Nat\s*:\s*Type/, "stdin must reach EOF and Lean must return before timeout");
  console.log("  - Lean stdin EOF delivery: PASS");

  const bareDir = fs.mkdtempSync(path.join(os.tmpdir(), "lean-exec-timeout-"));
  const origPath = process.env.PATH || "";
  try {
    const fakeBin = path.join(bareDir, "bin");
    fs.mkdirSync(fakeBin, { recursive: true });
    const fakeLean = path.join(fakeBin, "lean");
    fs.writeFileSync(fakeLean, "#!/bin/sh\nsleep 5\n", "utf-8");
    fs.chmodSync(fakeLean, 0o755);
    process.env.PATH = `${fakeBin}${path.delimiter}${origPath}`;
    const timeoutServer = new McpServer(bareDir);
    const frame = await timeoutServer.handleMessage({
      jsonrpc: "2.0",
      id: 99,
      method: "tools/call",
      params: {
        name: "lean_exec",
        arguments: { code: "#check Nat\n", timeoutMs: 1000 },
      },
    });
    assert.equal(frame?.result?.isError, true, "timeout_expired must surface as isError: true");
    const text = String(frame?.result?.content?.[0]?.text || "");
    assert.match(text, /^Error:\s*timeout_expired\b/, `expected timeout_expired output, got: ${text}`);
    console.log("  - Lean exec timeout_expired returns isError: true: PASS");

    const explicitBin = path.join(bareDir, "explicit-toolchain", "bin");
    fs.mkdirSync(explicitBin, { recursive: true });
    const explicitLean = path.join(explicitBin, "lean");
    fs.writeFileSync(
      explicitLean,
      "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then\n  echo \"Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit deadbeef, Release)\"\n  exit 0\nfi\nsleep 5\n",
      "utf-8",
    );
    fs.chmodSync(explicitLean, 0o755);
    const explicitModRoot = path.join(bareDir, "explicit-modules");
    fs.mkdirSync(explicitModRoot, { recursive: true });
    const explicitFrame = await timeoutServer.handleMessage({
      jsonrpc: "2.0",
      id: 100,
      method: "tools/call",
      params: {
        name: "lean_exec",
        arguments: {
          code: "#check Nat\n",
          timeoutMs: 1000,
          context: {
            compilerPath: explicitLean,
            targetVersion: "4.35.0",
            moduleRoots: [explicitModRoot],
          },
        },
      },
    });
    assert.equal(explicitFrame?.result?.isError, true, "explicit context timeout_expired must surface as isError: true");
    const explicitText = String(explicitFrame?.result?.content?.[0]?.text || "");
    assert.match(explicitText, /^Error:\s*timeout_expired\b/, `expected explicit timeout_expired output, got: ${explicitText}`);
    console.log("  - Lean exec explicit-context timeout_expired returns isError: true: PASS");
  } finally {
    process.env.PATH = origPath;
    fs.rmSync(bareDir, { recursive: true, force: true });
  }
} finally {
  fs.rmSync(projectRoot, { recursive: true, force: true });
}
