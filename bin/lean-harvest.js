#!/usr/bin/env node
// lean-harvest - Lean 4 corpus-wide linter findings harvester.
//
// Ports docs/easci/lean/scripts/lean_lint_harvest.sh to Node.js / ESM.
// Runs `lake env lean -D<flag>=true` per file across a parallel worker pool,
// tabulates findings per linter, and emits TSV or JSON reports.
//
// Usage:
//   lean-harvest <out.tsv> "<flag1> <flag2> ..." [files...]
//   lean-harvest --output <out.tsv> --flags "<flags>" [--jobs 8] [--timeout 300] [files...]
//
// Output format (TSV, one row per finding; --json for structured output):
//   linter\tfile\tline\tmessage
//     line    = the diagnostic's source line (0 when the line carries no
//               position)
//     message = the diagnostic text with its path:line:col: prefix removed
//               (the severity word is kept)
//   linter=COVERAGE rows mark a flag that was unknown for a module (invalid
//   -D option; the message holds the raw diagnostic line). One diagnostic
//   line can yield both a linter row and a COVERAGE row.
// Row semantics match the reference shell implementation
// (docs/easci/lean/scripts/lean_lint_harvest.sh); tests/test_harvest.mjs
// locks the format.

import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawn } from "node:child_process";

function parseArgs(argv) {
  const opts = {
    output: "",
    flags: [],
    files: [],
    jobs: parseInt(process.env.HARVEST_JOBS || "8", 10) || os.cpus().length || 4,
    timeoutMs: (parseInt(process.env.HARVEST_TIMEOUT || "300", 10) || 300) * 1000,
    pkgDir: process.cwd(),
    json: false,
  };

  const positional = [];
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--output" || a === "-o") {
      opts.output = argv[++i];
    } else if (a === "--flags" || a === "-f") {
      opts.flags = argv[++i].split(/\s+/).filter(Boolean);
    } else if (a === "--jobs" || a === "-j") {
      opts.jobs = parseInt(argv[++i], 10) || opts.jobs;
    } else if (a === "--timeout" || a === "-t") {
      opts.timeoutMs = (parseInt(argv[++i], 10) || 300) * 1000;
    } else if (a === "--pkg-dir" || a === "-d") {
      opts.pkgDir = path.resolve(argv[++i]);
    } else if (a === "--json") {
      opts.json = true;
    } else if (a === "--help" || a === "-h") {
      printHelp();
      process.exit(0);
    } else {
      positional.push(a);
    }
  }

  // Handle positional arguments if flags weren't named
  if (!opts.output && positional.length > 0) {
    opts.output = positional.shift();
  }
  if (opts.flags.length === 0 && positional.length > 0) {
    opts.flags = positional.shift().split(/\s+/).filter(Boolean);
  }
  if (positional.length > 0) {
    opts.files = positional;
  }

  return opts;
}

function printHelp() {
  console.log(`usage: lean-harvest <out.tsv> "<flag1> <flag2> ..." [files...]
Options:
  -o, --output <file>    Output TSV or JSON file
  -f, --flags <string>   Space-separated linter flags (e.g. "linter.style.header linter.style.haveILetI")
  -j, --jobs <n>         Concurrent worker processes (default: HARVEST_JOBS or 8)
  -t, --timeout <sec>    Timeout per Lean process in seconds (default: 300)
  -d, --pkg-dir <dir>    Lake package directory (default: cwd)
      --json             Output JSON instead of TSV
  -h, --help             Show this help`);
}

function findLeanFiles(dir) {
  const results = [];
  function walk(current) {
    let entries;
    try {
      entries = fs.readdirSync(current, { withFileTypes: true });
    } catch {
      return;
    }
    for (const ent of entries) {
      if (ent.name.startsWith(".") || ent.name === "node_modules" || ent.name === ".lake") continue;
      const full = path.join(current, ent.name);
      if (ent.isDirectory()) {
        walk(full);
      } else if (ent.isFile() && ent.name.endsWith(".lean")) {
        results.push(full);
      }
    }
  }
  walk(dir);
  return results;
}

function getPatternForLinter(flag) {
  switch (flag) {
    case "linter.style.header":
      return /header|doc-string/i;
    case "linter.style.multiGoal":
      return /multigoal|multiple goals/i;
    case "linter.style.haveILetI":
      return /haveilet|have/i;
    default:
      return null;
  }
}

function runLeanOnFile(pkgDir, flag, filePath, timeoutMs) {
  return new Promise((resolve) => {
    const child = spawn("lake", ["env", "lean", `-D${flag}=true`, filePath], {
      cwd: pkgDir,
      env: process.env,
      stdio: ["ignore", "pipe", "pipe"],
    });

    let output = "";
    child.stdout.on("data", (chunk) => { output += chunk.toString(); });
    child.stderr.on("data", (chunk) => { output += chunk.toString(); });

    const timer = setTimeout(() => {
      try { child.kill("SIGKILL"); } catch {}
      resolve({ output, timedOut: true });
    }, timeoutMs);

    child.on("close", () => {
      clearTimeout(timer);
      resolve({ output, timedOut: false });
    });

    child.on("error", (err) => {
      clearTimeout(timer);
      resolve({ output: String(err), timedOut: false, error: err });
    });
  });
}

function lineNumberOf(line) {
  // First :N: in the line (mirrors the shell reference's match()/substr).
  const m = line.match(/:(\d+):/);
  return m ? m[1] : "0";
}

function parseFindings(flag, filePath, output) {
  const findings = [];
  const pat = getPatternForLinter(flag);
  const lines = output.split(/\r?\n/);

  for (const line of lines) {
    // Rule 1: diagnostics (warning/error/information), filtered by the
    // per-linter pattern when one is known (null = keep every diagnostic).
    if (/^[^ ].*: (warning|error|information):/.test(line)) {
      if (!pat || pat.test(line)) {
        findings.push({
          linter: flag,
          file: filePath,
          line: lineNumberOf(line),
          message: line.replace(/^[^ ]*: /, ""),
        });
      }
    }
    // Rule 2: coverage marker - the flag's option was unknown for this
    // module, so the linter run did not cover it. Fires independently of
    // rule 1 (both rows can be emitted for the same line).
    if (line.includes("invalid -D parameter")) {
      findings.push({
        linter: "COVERAGE",
        file: filePath,
        line: lineNumberOf(line),
        message: line,
      });
    }
  }

  return findings;
}

async function runPool(tasks, concurrency, workerFn) {
  const results = [];
  let index = 0;

  async function worker() {
    while (index < tasks.length) {
      const currentIndex = index++;
      const res = await workerFn(tasks[currentIndex]);
      results.push(res);
    }
  }

  const workers = Array.from({ length: Math.min(concurrency, tasks.length) }, () => worker());
  await Promise.all(workers);
  return results;
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));

  if (!opts.output) {
    console.error("error: missing output file");
    printHelp();
    process.exit(2);
  }
  if (opts.flags.length === 0) {
    console.error("error: missing linter flags");
    printHelp();
    process.exit(2);
  }

  // Resolve target files
  let targetFiles = opts.files;
  if (targetFiles.length === 0) {
    const defaultSearch = path.join(opts.pkgDir, "EASCI");
    if (fs.existsSync(defaultSearch)) {
      targetFiles = findLeanFiles(defaultSearch);
    } else {
      targetFiles = findLeanFiles(opts.pkgDir);
    }
  }

  // Normalize paths relative to pkgDir if inside
  targetFiles = targetFiles.map((f) => {
    const rel = path.relative(opts.pkgDir, path.resolve(f));
    return rel.startsWith("..") ? path.resolve(f) : rel;
  });

  const totalTasks = [];
  for (const f of targetFiles) {
    for (const flag of opts.flags) {
      totalTasks.push({ file: f, flag });
    }
  }

  const allFindings = [];

  await runPool(totalTasks, opts.jobs, async (task) => {
    const { output } = await runLeanOnFile(opts.pkgDir, task.flag, task.file, opts.timeoutMs);
    const findings = parseFindings(task.flag, task.file, output);
    allFindings.push(...findings);
  });

  // Write output
  if (opts.json) {
    fs.writeFileSync(opts.output, JSON.stringify(allFindings, null, 2), "utf-8");
  } else {
    const tsvLines = allFindings.map(
      (f) => `${f.linter}\t${f.file}\t${f.line}\t${f.message}`
    );
    fs.writeFileSync(opts.output, tsvLines.join("\n") + (tsvLines.length ? "\n" : ""), "utf-8");
  }

  // Summary statistics
  const countsByLinter = {};
  for (const f of allFindings) {
    countsByLinter[f.linter] = (countsByLinter[f.linter] || 0) + 1;
  }

  console.log(`== harvest: ${opts.flags.join(" ")} ==`);
  console.log(`   files scanned : ${targetFiles.length}`);
  console.log(`   findings      : ${allFindings.length}`);
  const sortedLinters = Object.keys(countsByLinter).sort();
  for (const linter of sortedLinters) {
    console.log(`   ${linter.padEnd(28)} ${countsByLinter[linter]}`);
  }
}

main().catch((err) => {
  console.error("fatal error:", err);
  process.exit(1);
});
