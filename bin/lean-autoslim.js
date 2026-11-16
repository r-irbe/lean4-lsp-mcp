#!/usr/bin/env node
// bin/lean-autoslim.js
// CLI entrypoint for the kernel-verified Lean 4 proof auto-slimmer.
// Wires lean-analyzer ALTPROOF-ROUTE quickfix spans to real Lean 4 elaboration
// (Virtual LSP via FileWorkerManager or batch lake env lean) and accepts only
// strictly shorter, 0-error / 0-warning / 0-sorry replacements.
// Scoped Unicode policy (INV-001; typographic-free by default).

import * as fs from "node:fs";
import * as path from "node:path";
import { spawn } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");

const USAGE = [
  "Usage: lean-autoslim <file.lean> [options]",
  "",
  "Options:",
  "  --apply                   Atomically write verified slimmed proofs to disk (default: dry-run)",
  "  --mode <auto|lsp|batch>   Verification backend (default: auto)",
  "  --allow-altproof-import   Allow inserting project AltProof / Tactics import when needed",
  "  --route <id>              Whitelist altproof route ID (repeatable or comma-separated)",
  "  --max-candidates <n>      Maximum number of candidates to probe (default: 50)",
  "  --timeout-ms <ms>         Per-candidate Lean timeout in ms (default: 25000)",
  "  --json                    Emit machine-readable JSON report (default)",
  "  --markdown                Emit human-readable Markdown report + diff",
  "  -h, --help                Show this help message",
].join("\n");

export function parseAutoSlimCliArgs(argv) {
  const opts = {
    filePath: "",
    apply: false,
    mode: "auto",
    allowAltProofImport: false,
    routes: [],
    maxCandidates: 50,
    timeoutMs: 25000,
    format: "json",
    help: false,
  };

  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "-h" || a === "--help") {
      opts.help = true;
      continue;
    }
    if (a === "--apply") {
      opts.apply = true;
      continue;
    }
    if (a === "--dry-run") {
      opts.apply = false;
      continue;
    }
    if (a === "--allow-altproof-import") {
      opts.allowAltProofImport = true;
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
    if (flag === "--mode") {
      const m = takeVal().toLowerCase();
      if (m !== "auto" && m !== "lsp" && m !== "batch") {
        throw new Error(`Invalid --mode '${m}' (expected auto|lsp|batch)`);
      }
      opts.mode = m;
    } else if (flag === "--route" || flag === "--routes") {
      const parts = takeVal()
        .split(",")
        .map((s) => s.trim())
        .filter(Boolean);
      opts.routes.push(...parts);
    } else if (flag === "--max-candidates") {
      opts.maxCandidates = Number.parseInt(takeVal(), 10) || 50;
    } else if (flag === "--timeout-ms") {
      opts.timeoutMs = Number.parseInt(takeVal(), 10) || 25000;
    } else if (flag === "--format") {
      const fmt = takeVal().toLowerCase();
      opts.format = fmt === "markdown" ? "markdown" : "json";
    } else if (a.startsWith("-")) {
      throw new Error(`Unknown option: ${a}`);
    } else if (!opts.filePath) {
      opts.filePath = a;
    } else {
      throw new Error(`Unexpected extra positional argument: ${a}`);
    }
  }
  return opts;
}

async function runCli() {
  let opts;
  try {
    opts = parseAutoSlimCliArgs(process.argv.slice(2));
  } catch (err) {
    process.stderr.write(`Error: ${err instanceof Error ? err.message : String(err)}\n${USAGE}\n`);
    process.exit(2);
  }
  if (opts.help) {
    process.stdout.write(`${USAGE}\n`);
    return;
  }
  if (!opts.filePath) {
    process.stderr.write(`Error: missing target <file.lean>\n${USAGE}\n`);
    process.exit(2);
  }

  const distEntry = path.resolve(pkgRoot, "dist/index.js");
  const distRootEntry = path.resolve(pkgRoot, "dist/project_root.js");
  const srcEntry = path.resolve(pkgRoot, "src/index.ts");
  const srcRootEntry = path.resolve(pkgRoot, "src/project_root.ts");
  let mod;
  let rootMod;
  if (fs.existsSync(distEntry) && fs.existsSync(distRootEntry)) {
    mod = await import(pathToFileURL(distEntry).href);
    rootMod = await import(pathToFileURL(distRootEntry).href);
  } else if (process.execArgv.includes("--experimental-strip-types")) {
    mod = await import(pathToFileURL(srcEntry).href);
    rootMod = await import(pathToFileURL(srcRootEntry).href);
  } else {
    const child = spawn(
      process.execPath,
      ["--experimental-strip-types", fileURLToPath(import.meta.url), ...process.argv.slice(2)],
      { stdio: "inherit" }
    );
    child.on("exit", (code) => process.exit(code ?? 1));
    return;
  }

  const absTarget = path.resolve(process.cwd(), opts.filePath);
  const resolvedRoot = (mod.resolveProjectRoot || rootMod.resolveProjectRoot)(path.dirname(absTarget));
  const manager = new mod.FileWorkerManager(resolvedRoot.root);
  try {
    const out = await manager.autoSlimFile({
      filePath: absTarget,
      apply: opts.apply,
      mode: opts.mode,
      allowAltProofImport: opts.allowAltProofImport,
      routes: opts.routes.length > 0 ? opts.routes : undefined,
      maxCandidates: opts.maxCandidates,
      timeoutMs: opts.timeoutMs,
      format: opts.format,
    });
    process.stdout.write(`${out}\n`);
  } catch (err) {
    process.stderr.write(`lean-autoslim error: ${err instanceof Error ? err.message : String(err)}\n`);
    process.exit(1);
  } finally {
    manager.dispose();
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runCli();
}
