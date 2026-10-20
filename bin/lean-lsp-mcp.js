#!/usr/bin/env node
// bin/lean-lsp-mcp.js
// Executable entrypoint for lean-lsp-mcp stdio server.
// Strict 7-bit ASCII only (INV-001).

import * as fs from "node:fs";
import * as path from "node:path";
import { spawn } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const distEntry = path.resolve(__dirname, "../dist/index.js");
const srcEntry = path.resolve(__dirname, "../src/index.ts");

if (fs.existsSync(distEntry)) {
  await import(pathToFileURL(distEntry).href);
} else {
  const child = spawn(
    process.execPath,
    ["--experimental-strip-types", srcEntry, ...process.argv.slice(2)],
    { stdio: "inherit" }
  );
  child.on("exit", (code) => {
    process.exit(code ?? 0);
  });
}
