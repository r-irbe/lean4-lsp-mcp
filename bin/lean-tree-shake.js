#!/usr/bin/env node
// bin/lean-tree-shake.js
// CLI entrypoint for Lean 4 declaration-level & module-level tree-shaking.
// Scoped Unicode policy (INV-001; strict 7-bit ASCII source).

import * as fs from "node:fs";
import * as path from "node:path";
import { spawn } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");

const USAGE = [
  "Usage: lean-tree-shake <EntryModuleOrFile...> [options]",
  "",
  "Options:",
  "  --project-root <dir>              Lake project root (default: cwd)",
  "  --output-dir <dir>                Emit standalone Lake slice into <dir>",
  "  --archive <path.tar.gz>           Emit deterministic, metadata-scrubbed .tar.gz archive",
  "  --granularity <declaration|module> Pruning level (default: declaration)",
  "  --anonymize                       Scrub author/copyright headers and repo URLs for double-blind review",
  "  --package-name <name>             Override package name in emitted lakefile/manifest",
  "  --forbid <pattern>                Case-insensitive leak pattern to forbid (repeatable or comma-separated)",
  "  --verify-build                    Verify standalone `lake build` on emitted slice",
  "  --timeout-ms <ms>                 Build verification timeout in ms (default: 600000)",
  "  --json                            Emit JSON report (default)",
  "  --markdown                        Emit Markdown summary report",
  "  -h, --help                        Show this help message",
].join("\n");

export function parseTreeShakeCliArgs(argv) {
  const opts = {
    projectRoot: process.cwd(),
    entryModules: [],
    outputDir: undefined,
    archivePath: undefined,
    granularity: "declaration",
    anonymize: false,
    packageName: undefined,
    forbiddenPatterns: [],
    verifyBuild: false,
    timeoutMs: 600000,
    format: "json",
    help: false,
  };

  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "-h" || a === "--help") {
      opts.help = true;
      continue;
    }
    if (a === "--anonymize") {
      opts.anonymize = true;
      continue;
    }
    if (a === "--verify-build") {
      opts.verifyBuild = true;
      continue;
    }
    if (a === "--json") {
      opts.format = "json";
      continue;
    }
    if (a === "--markdown") {
      opts.format = "markdown";
      continue;
    }
    const eqIdx = a.startsWith("--") ? a.indexOf("=") : -1;
    const flag = eqIdx >= 0 ? a.slice(0, eqIdx) : a;
    const inlineVal = eqIdx >= 0 ? a.slice(eqIdx + 1) : undefined;
    const takeVal = () => {
      if (inlineVal !== undefined) return inlineVal;
      if (i + 1 >= argv.length) throw new Error(`Missing value for ${flag}`);
      i++;
      return argv[i];
    };

    if (flag === "--project-root" || flag === "-d") {
      opts.projectRoot = path.resolve(takeVal());
    } else if (flag === "--output-dir" || flag === "-o") {
      opts.outputDir = path.resolve(takeVal());
    } else if (flag === "--archive") {
      opts.archivePath = path.resolve(takeVal());
    } else if (flag === "--granularity") {
      const g = takeVal().toLowerCase();
      if (g !== "declaration" && g !== "module") {
        throw new Error(`Invalid --granularity '${g}' (expected declaration|module)`);
      }
      opts.granularity = g;
    } else if (flag === "--package-name") {
      opts.packageName = takeVal().trim();
    } else if (flag === "--forbid") {
      const parts = takeVal()
        .split(",")
        .map((s) => s.trim())
        .filter(Boolean);
      opts.forbiddenPatterns.push(...parts);
    } else if (flag === "--timeout-ms") {
      opts.timeoutMs = Number.parseInt(takeVal(), 10) || 600000;
    } else if (flag === "--format") {
      opts.format = takeVal().toLowerCase() === "markdown" ? "markdown" : "json";
    } else if (a.startsWith("-")) {
      throw new Error(`Unknown option: ${a}`);
    } else {
      opts.entryModules.push(a);
    }
  }
  return opts;
}

async function runCli() {
  let opts;
  try {
    opts = parseTreeShakeCliArgs(process.argv.slice(2));
  } catch (err) {
    process.stderr.write(`Error: ${err instanceof Error ? err.message : String(err)}\n${USAGE}\n`);
    process.exit(2);
  }
  if (opts.help) {
    process.stdout.write(`${USAGE}\n`);
    return;
  }
  if (opts.entryModules.length === 0) {
    process.stderr.write(`Error: Missing <EntryModuleOrFile...>\n${USAGE}\n`);
    process.exit(2);
  }

  const distPath = path.join(pkgRoot, "dist", "tree_shake.js");
  const srcPath = path.join(pkgRoot, "src", "tree_shake.ts");

  let mod;
  if (fs.existsSync(distPath)) {
    mod = await import(pathToFileURL(distPath).href);
  } else if (fs.existsSync(srcPath)) {
    if (!process.execArgv.includes("--experimental-strip-types")) {
      const child = spawn(
        process.execPath,
        ["--experimental-strip-types", fileURLToPath(import.meta.url), ...process.argv.slice(2)],
        { stdio: "inherit" }
      );
      child.on("exit", (code) => process.exit(code ?? 1));
      return;
    }
    mod = await import(pathToFileURL(srcPath).href);
  } else {
    process.stderr.write("Error: Unable to locate dist/tree_shake.js or src/tree_shake.ts\n");
    process.exit(1);
  }

  const report = await mod.runLeanTreeShake(opts);
  if (opts.format === "markdown") {
    process.stdout.write(`${mod.formatTreeShakeMarkdown(report)}\n`);
  } else {
    process.stdout.write(`${JSON.stringify(report, null, 2)}\n`);
  }
  if (opts.verifyBuild && !report.buildVerified) {
    process.exit(1);
  }
  if (report.anonymityLeakHits.length > 0) {
    process.exit(1);
  }
}

const isMain =
  process.argv[1] &&
  path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url));
if (isMain) {
  runCli().catch((err) => {
    process.stderr.write(`Fatal error: ${err instanceof Error ? err.message : String(err)}\n`);
    process.exit(1);
  });
}
