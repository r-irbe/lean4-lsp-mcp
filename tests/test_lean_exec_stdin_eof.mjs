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
} finally {
  fs.rmSync(projectRoot, { recursive: true, force: true });
}
