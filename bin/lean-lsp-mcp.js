#!/usr/bin/env node
// bin/lean-lsp-mcp.js
// Executable entrypoint for lean-lsp-mcp stdio server.
// Scoped Unicode policy (INV-001; typographic-free by default).

import * as fs from "node:fs";
import * as path from "node:path";
import { spawn, spawnSync } from "node:child_process";
import { createRequire } from "node:module";
import { fileURLToPath, pathToFileURL } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
const pkgJsonPath = path.resolve(pkgRoot, "package.json");
const lockPath = path.resolve(pkgRoot, "package-lock.json");
const distEntry = path.resolve(pkgRoot, "dist/index.js");
const srcEntry = path.resolve(pkgRoot, "src/index.ts");
const installedPackage = pkgRoot.split(path.sep).includes("node_modules");
const hasDistEntry = fs.existsSync(distEntry);
const require = createRequire(import.meta.url);

function hasRuntimeDependencies() {
  try {
    require.resolve("@modelcontextprotocol/sdk/package.json");
    require.resolve("js-yaml");
    return true;
  } catch {
    return false;
  }
}

if (installedPackage && !hasDistEntry) {
  process.stderr.write("[lean-lsp-mcp] ERROR: Installed package is missing dist/index.js. Reinstall a built package.\n");
  process.exit(1);
}

const runtimeDependenciesAvailable = hasRuntimeDependencies();
if (installedPackage && !runtimeDependenciesAvailable) {
  process.stderr.write("[lean-lsp-mcp] ERROR: Missing runtime dependencies. Reinstall lean4-lsp-mcp.\n");
  process.exit(1);
}

// An npm install can hoist dependencies above the package's own node_modules.
// Direct all npm output to stderr so MCP stdio JSON-RPC on stdout is never polluted.
if (!runtimeDependenciesAvailable && fs.existsSync(pkgJsonPath)) {
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
  if (!hasRuntimeDependencies()) {
    const exitCode = res.status || 1;
    process.stderr.write(
      `[lean-lsp-mcp] ERROR: Failed to bootstrap node_modules (exit ${exitCode}). Run 'npm install' in ${pkgRoot}.\n`
    );
    process.exit(exitCode);
  }
}

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
  !installedPackage &&
  fs.existsSync(srcEntry) &&
  (!hasDistEntry || fs.statSync(srcEntry).mtimeMs > fs.statSync(distEntry).mtimeMs);

if (hasDistEntry && !(supportsStripTypes && srcNewerThanDist)) {
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
