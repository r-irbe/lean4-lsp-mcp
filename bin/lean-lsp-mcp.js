#!/usr/bin/env node
// bin/lean-lsp-mcp.js
// Executable entrypoint for lean-lsp-mcp stdio server.
// Scoped Unicode policy (INV-001; typographic-free by default).

import * as fs from "node:fs";
import * as path from "node:path";
import { spawn, spawnSync } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
const sdkPath = path.resolve(pkgRoot, "node_modules/@modelcontextprotocol/sdk");
const pkgJsonPath = path.resolve(pkgRoot, "package.json");
const lockPath = path.resolve(pkgRoot, "package-lock.json");

// Auto-bootstrap runtime npm dependencies on first launch if node_modules is missing.
// Direct all npm output to stderr so MCP stdio JSON-RPC on stdout is never polluted.
if (!fs.existsSync(sdkPath) && fs.existsSync(pkgJsonPath)) {
  const npmCmd = process.platform === "win32" ? "npm.cmd" : "npm";
  const subCmd = fs.existsSync(lockPath) ? "ci" : "install";
  process.stderr.write(
    `[lean-lsp-mcp] Bootstrapping runtime dependencies (npm ${subCmd} --omit=dev)...\n`
  );
  const res = spawnSync(
    npmCmd,
    [subCmd, "--omit=dev", "--no-audit", "--no-fund", "--loglevel=error"],
    {
      cwd: pkgRoot,
      stdio: ["ignore", "pipe", "inherit"]
    }
  );
  if (res.stdout && res.stdout.length > 0) {
    process.stderr.write(res.stdout);
  }
  if (res.status !== 0 && !fs.existsSync(sdkPath)) {
    process.stderr.write(
      `[lean-lsp-mcp] ERROR: Failed to bootstrap node_modules (exit ${res.status ?? 1}). Run 'npm install' in ${pkgRoot}.\n`
    );
    process.exit(res.status ?? 1);
  }
}

const distEntry = path.resolve(pkgRoot, "dist/index.js");
const srcEntry = path.resolve(pkgRoot, "src/index.ts");

// Forward --lake-roots CLI flag into LEAN_LAKE_ROOTS for both dist and strip-types entrypoints.
const cliArgs = process.argv.slice(2);
for (let i = 0; i < cliArgs.length; i++) {
  const arg = cliArgs[i];
  if (arg === "--lake-roots" && cliArgs[i + 1]) {
    process.env.LEAN_LAKE_ROOTS = cliArgs[i + 1];
    i++;
  } else if (arg.startsWith("--lake-roots=")) {
    process.env.LEAN_LAKE_ROOTS = arg.slice("--lake-roots=".length);
  }
}

const nodeMajor = Number.parseInt(process.versions.node.split(".")[0] || "0", 10);
const nodeMinor = Number.parseInt(process.versions.node.split(".")[1] || "0", 10);
const supportsStripTypes = nodeMajor > 22 || (nodeMajor === 22 && nodeMinor >= 6);
const srcNewerThanDist =
  fs.existsSync(srcEntry) &&
  (!fs.existsSync(distEntry) || fs.statSync(srcEntry).mtimeMs > fs.statSync(distEntry).mtimeMs);

if (fs.existsSync(distEntry) && !(supportsStripTypes && srcNewerThanDist)) {
  const mod = await import(pathToFileURL(distEntry).href);
  if (typeof mod.main === "function") {
    mod.main();
  }
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
