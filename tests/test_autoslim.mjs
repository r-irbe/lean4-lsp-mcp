// tests/test_autoslim.mjs
// Unit and end-to-end tests for the kernel-verified proof auto-slimmer (lean_autoslim + lean-autoslim CLI).
// Covers:
// 1. UTF-16 LSP range-to-string slicing across multi-byte math symbols (\u2211, \u2115, \u211d, \u2264)
// 2. Discovery of exact `by ...` quickfix spans via bundled `bin/lean-analyzer`
// 3. Virtual LSP verifier acceptance/rejection, cumulative multi-edit drift handling, and dry-run non-mutation
// 4. Atomic apply (`apply: true`) + optional `allowAltProofImport` + `McpServer.executeTool("lean_autoslim", ...)`
// 5. CLI argument parser (`bin/lean-autoslim.js`)
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { createHash } from "node:crypto";
import {
  buildCandidateTacticList,
  computeUtf16LineOffsets,
  detectAltProofAvailability,
  discoverAutoSlimCandidates,
  lspRangeToStringOffsets,
  runKernelVerifiedAutoSlim,
  runBatchLeanCheck,
} from "../src/autoslim.ts";
import * as autoslimHelpers from "../src/autoslim.ts";
import { McpServer, TOOL_DEFINITIONS, FileWorkerManager } from "../src/index.ts";
import { isWholeTheoremProof, isSafeProofReplacement } from "../src/lean_source.ts";
import { parseAutoSlimCliArgs } from "../bin/lean-autoslim.js";

function safetyFixture() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-safety-"));
  fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "demo"\n');
  const file = path.join(root, "Sample.lean");
  const source = [
    "theorem keep_named (a b c d : Nat) (ha : a = b) (hb : b = c)",
    "    (hc : c = d) (hd : d = d) : a = d := by",
    "  rw [ha]",
    "  rw [hb]",
    "  rw [hc]",
    "  rw [hd]",
    "",
    "theorem neighbour (ha : True) : True := by exact ha",
    "",
  ].join("\n");
  fs.writeFileSync(file, source);
  return { root, file, source };
}

function fixtureAnalyzer(root, diagnostic, mutate = "") {
  const bin = path.join(root, "analyzer.mjs");
  fs.writeFileSync(bin, `#!${process.execPath}\nimport fs from "node:fs";\n${mutate}\nconsole.log(${JSON.stringify(JSON.stringify({ files: [{ diagnostics: [diagnostic] }] }))});\n`);
  fs.chmodSync(bin, 0o755);
  return bin;
}

function fixtureDiagnostic(source, replacement = "by grind") {
  return {
    code: "ALTPROOF-ROUTE", operator: "keep_named", altproof_route: "eqsat-congruence-closure",
    quickfix: { range: { start: { line: 1, character: source.split("\n")[1].indexOf("by") },
      end: { line: 5, character: "  rw [hd]".length } }, new_text: replacement },
  };
}

test("structural proof proposals retain explicit unfold hints and mask comments", () => {
  assert.deepEqual(autoslimHelpers.buildUnfoldingTactics("by\n  unfold Demo.distance at h\n  /- unfold Wrong -/\n  grind"),
    ["by simp_all [Demo.distance]", "by grind [Demo.distance]", "by simp [Demo.distance]"]);
  assert.deepEqual(autoslimHelpers.buildUnfoldingTactics('by\n  let s := "unfold Wrong"\n  trivial'), []);
});

test("proof boundary rejects opaque commands, later definitions, and type-level proofs", () => {
  for (const [source, needle] of [
    ["theorem a : True := by trivial\nopaque marker : Nat := 37\n", "by trivial"],
    ["theorem a : True := by trivial\ndef second : Nat := by exact 12345\n", "by exact"],
    ["theorem a : let T := by exact True; T := by trivial\n", "by exact"],
  ]) {
    assert.equal(isWholeTheoremProof(source, source.indexOf(needle), source.trimEnd().length, "a"), false);
  }
  assert.equal(isSafeProofReplacement("by trivial\nopaque marker : Nat := 37"), false);
});

test("autoslim refuses malformed UTF-8 without changing any original bytes", async () => {
  const { root, file, source } = safetyFixture();
  const bytes = Buffer.concat([Buffer.from(source + "-- "), Buffer.from([0xff])]);
  fs.writeFileSync(file, bytes);
  try {
    await assert.rejects(runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp",
      lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 0 }),
    }), /UTF-8/);
    assert.deepEqual(fs.readFileSync(file), bytes);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim never removes another invocation's existing temporary file", async () => {
  const { root, file } = safetyFixture();
  const foreign = path.join(root, `.autoslim_apply_${process.pid}_${createHash("sha256").update(file).digest("hex").slice(0, 8)}.tmp`);
  fs.writeFileSync(foreign, "foreign temp contents");
  try {
    try {
      await runKernelVerifiedAutoSlim(root, { filePath: file, apply: true, mode: "lsp",
        lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 0 }) });
    } catch (error) { assert.equal(error.code, "EEXIST"); }
    assert.equal(fs.readFileSync(foreign, "utf8"), "foreign temp contents");
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("manager refuses stale or absent LSP diagnostic versions for an edited candidate", async () => {
  const { root, file } = safetyFixture();
  const manager = new FileWorkerManager(root);
  const uri = "file://" + file;
  const session = { leanRoot: root, child: { kill() {} }, openFiles: new Map([[file, { version: 1 }]]),
    diagnostics: new Map([[uri, { version: 1, diags: [], ts: Date.now() }]]),
    progress: new Map([[uri, { version: 1, pending: 0, ts: Date.now() }]]) };
  manager["sessions"].set(root, session);
  manager["ensureSession"] = async () => session;
  manager["syncDocument"] = () => uri;
  manager["waitForAnalysis"] = async () => true;
  manager["sendNotification"] = () => {};
  try {
    const result = JSON.parse(await manager.autoSlimFile({ filePath: file, mode: "lsp" }));
    assert.equal(result.verifiedCount, 0);
    assert.match(result.rejected[0].lastDiagnostic, /version|evidence/i);
  } finally { manager.dispose(); fs.rmSync(root, { recursive: true, force: true }); }
});

test("CLI emits a partial batch receipt and a failing exit status", () => {
  const { root, file } = safetyFixture();
  fs.writeFileSync(file, "theorem clean : True := by trivial\n");
  try {
    let output;
    try {
      output = execFileSync(process.execPath, [fileURLToPath(new URL("../bin/lean-autoslim.js", import.meta.url)),
        file, path.join(root, "Missing.lean"), "--json"], { encoding: "utf8" });
      assert.fail("partial batch must exit nonzero");
    } catch (error) { assert.equal(error.status, 1); output = error.stdout; }
    const report = JSON.parse(output);
    assert.equal(report.completed, false);
    assert.equal(report.reports.length, 1);
    assert.equal(report.failures.length, 1);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim preserves concurrent edits made during verification", async () => {
  const { root, file, source } = safetyFixture();
  const foreign = source + "-- concurrent writer's work\n";
  try {
    await assert.rejects(runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp",
      lspVerifier: async () => {
        fs.writeFileSync(file, foreign);
        return { ok: true, errorCount: 0, warningCount: 0 };
      },
    }), /source.*changed/i);
    assert.equal(fs.readFileSync(file, "utf8"), foreign);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim rejects source changed by the analyzer before using its ranges", async () => {
  const { root, file, source } = safetyFixture();
  const changed = "-- shifted during discovery\n" + source;
  try {
    const analyzerBin = fixtureAnalyzer(root, fixtureDiagnostic(source),
      `fs.writeFileSync(process.argv[3], ${JSON.stringify(changed)});`);
    await assert.rejects(runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp", analyzerBin,
      lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 0 }),
    }), /source.*changed/i);
    assert.equal(fs.readFileSync(file, "utf8"), changed);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim rejects a proof range that swallows a neighbouring theorem header", async () => {
  const { root, file, source } = safetyFixture();
  try {
    const diag = fixtureDiagnostic(source);
    diag.quickfix.range.end = { line: 7, character: source.split("\n")[7].length };
    const report = await runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp", analyzerBin: fixtureAnalyzer(root, diag),
      lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 0 }),
    });
    assert.equal(report.verifiedCount, 0);
    assert.equal(fs.readFileSync(file, "utf8"), source);
    assert.match(report.rejected[0].reason, /proof.*boundary|declaration/);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim rejects sorry proposals even when a verifier reports success", async () => {
  const { root, file, source } = safetyFixture();
  try {
    const diag = fixtureDiagnostic(source, "by sorry");
    diag.altproof_route = "test-no-fallback";
    const report = await runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp", analyzerBin: fixtureAnalyzer(root, diag),
      lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 0 }),
    });
    assert.equal(report.verifiedCount, 0);
    assert.equal(fs.readFileSync(file, "utf8"), source);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim never accepts a verifier verdict carrying warnings", async () => {
  const { root, file, source } = safetyFixture();
  try {
    const report = await runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp",
      lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 1 }),
    });
    assert.equal(report.verifiedCount, 0);
    assert.equal(fs.readFileSync(file, "utf8"), source);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("autoslim receipts bind accepted proof edits to source hashes, signatures and timing", async () => {
  const { root, file, source } = safetyFixture();
  try {
    const report = await runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "lsp",
      lspVerifier: async () => ({ ok: true, errorCount: 0, warningCount: 0 }),
    });
    assert.equal(report.verifiedCount, 1);
    assert.equal(report.signaturesPreserved, true);
    assert.equal(report.candidatesConsidered, 1);
    assert.equal(report.candidatesDeferred, 0);
    assert.match(report.sourceHashBefore, /^[a-f0-9]{64}$/);
    assert.notEqual(report.sourceHashBefore, report.sourceHashAfter);
    assert.ok(report.verificationTimeMs >= 0);
    assert.equal(fs.readFileSync(file, "utf8").split(":= by")[0], source.split(":= by")[0]);
    assert.match(fs.readFileSync(file, "utf8"), /theorem neighbour \(ha : True\)/);
  } finally { fs.rmSync(root, { recursive: true, force: true }); }
});

test("CLI and MCP accept a deduplicated batch and report per-file failures", async () => {
  const opts = parseAutoSlimCliArgs(["One.lean", "Two.lean", "--apply"]);
  assert.deepEqual(opts.filePaths, ["One.lean", "Two.lean"]);
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-batch-"));
  fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "demo"\n');
  fs.writeFileSync(path.join(root, "One.lean"), "theorem one : True := by trivial\n");
  const server = new McpServer(root);
  try {
    const out = JSON.parse(await server.executeTool("lean_autoslim", {
      filePaths: ["One.lean", "Missing.lean", "One.lean"],
    }));
    assert.equal(out.kind, "batch");
    assert.equal(out.filesRequested, 2);
    assert.equal(out.reports.length, 1);
    assert.equal(out.failures.length, 1);
    assert.match(out.failures[0].error, /not found/i);
    assert.equal(out.verifiedCount, 0);
    assert.equal(out.completed, false);
  } finally { server.dispose(); fs.rmSync(root, { recursive: true, force: true }); }
});

test("real Lean accepts signature-preserving fixes and rejects errors and sorry", {
  skip: !process.env.LEAN_AUTOSLIM_INTEGRATION_ROOT,
}, async () => {
  const root = path.resolve(process.env.LEAN_AUTOSLIM_INTEGRATION_ROOT);
  const dir = fs.mkdtempSync(path.join(root, ".autoslim-integration-"));
  const file = path.join(dir, "Sample.lean");
  const source = "import Mathlib.Tactic\nset_option autoImplicit false\n" +
    "theorem named (P : Prop) (ha : P) : P /\\ P := by constructor <;> exact ha\n";
  fs.writeFileSync(file, source);
  try {
    const report = await runKernelVerifiedAutoSlim(root, {
      filePath: file, apply: true, mode: "batch", timeoutMs: 30000,
    });
    assert.equal(report.verifiedCount, 1);
    assert.equal(report.applied, true);
    assert.match(fs.readFileSync(file, "utf8"), /\(ha : P\).*:= by grind/);
    for (const proof of ["by trivial", "by sorry"]) {
      const verdict = await runBatchLeanCheck(root, dir,
        `import Mathlib.Tactic\ntheorem rejected : False := ${proof}\n`, 30000);
      assert.equal(verdict.ok, false, proof);
    }
  } finally { fs.rmSync(dir, { recursive: true, force: true }); }
});

test("UTF-16 LSP range offsets slice multi-line proofs with Unicode math symbols accurately", () => {
  const src = [
    "import MyProject.Tactics",
    "",
    "theorem utf16_demo (s : Finset \u2115) (f : \u2115 \u2192 \u211d) : \u2211 i \u2208 s, (f i + 0) = \u2211 i \u2208 s, f i := by",
    "  apply Finset.sum_congr rfl",
    "  intro i _hi",
    "  ring -- keep trailing comment",
    "",
    "/-- Next docstring stays intact. -/",
    "theorem keep_me : 1 = 1 := by rfl",
    "",
  ].join("\n");

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-utf16-"));
  try {
    const filePath = path.join(tmpDir, "Demo.lean");
    fs.writeFileSync(filePath, src, "utf-8");

    const cands = discoverAutoSlimCandidates(filePath, { allowCustomAltProof: true });
    assert.equal(cands.length, 1);
    assert.equal(cands[0].theoremName, "utf16_demo");
    assert.equal(cands[0].route, "sum_congr_ring");

    const offsets = computeUtf16LineOffsets(src);
    const span = lspRangeToStringOffsets(src, offsets, cands[0].range);
    assert.ok(span, "Expected valid UTF-16 string offsets");
    const sliced = src.slice(span.startIdx, span.endIdx);
    assert.ok(sliced.startsWith("by\n  apply Finset.sum_congr rfl"), `Unexpected slice start: ${sliced}`);
    assert.ok(sliced.endsWith("  ring"), `Unexpected slice end: ${sliced}`);
    assert.ok(!sliced.includes("keep trailing comment"), "Slice must exclude trailing comment");
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});

test("buildCandidateTacticList respects allowCustomAltProof and preserves core/Mathlib fallbacks", () => {
  const withAlt = buildCandidateTacticList("eqsat-congruence-closure", "by eqsat_rw", true);
  assert.deepEqual(withAlt, ["by eqsat_rw", "by grind_close", "by grind", "by simp"]);

  const withoutAlt = buildCandidateTacticList("eqsat-congruence-closure", "by eqsat_rw", false);
  assert.deepEqual(withoutAlt, ["by grind", "by simp"]);
});

test("runKernelVerifiedAutoSlim cascades past rejected tactics, accumulates multiple edits, and honors dryRun vs apply", async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-cascade-"));
  try {
    fs.writeFileSync(path.join(tmpDir, "lakefile.toml"), 'name = "demo"\n', "utf-8");
    fs.mkdirSync(path.join(tmpDir, "MyProject"), { recursive: true });
    fs.writeFileSync(
      path.join(tmpDir, "MyProject", "Tactics.lean"),
      'import ProofSkills.AltProof\nelab "sum_congr_ring" : tactic => pure ()\n',
      "utf-8"
    );

    const leanFile = path.join(tmpDir, "Sample.lean");
    const original = [
      "import Mathlib",
      "",
      "theorem first_sum (s : Finset \u2115) (f : \u2115 \u2192 \u211d) : \u2211 i \u2208 s, (f i + 0) = \u2211 i \u2208 s, f i := by",
      "  apply Finset.sum_congr rfl",
      "  intro i _hi",
      "  ring",
      "",
      "theorem second_eqsat (a b c d : \u2115) (h1 : a = b) (h2 : b = c) (h3 : c = d) (h4 : d = d) : a = d := by",
      "  rw [h1]",
      "  rw [h2]",
      "  rw [h3]",
      "  rw [h4]",
      "",
      "theorem third_unslimmable (s : Finset \u2115) (f : \u2115 \u2192 \u211d) : 0 \u2264 \u2211 i \u2208 s, f i ^ 2 := by",
      "  apply Finset.sum_nonneg",
      "  intro i _hi",
      "  exact sq_nonneg (f i)",
      "",
    ].join("\n");
    fs.writeFileSync(leanFile, original, "utf-8");

    const avail = detectAltProofAvailability(original, tmpDir);
    assert.equal(avail.importedInFile, false);
    assert.equal(avail.availableModule, "MyProject.Tactics");

    // Mock Virtual LSP verifier:
    // - Accepts `by sum_congr_ring` (with `import MyProject.Tactics` inserted!) on `first_sum`
    // - Rejects `by eqsat_rw` and `by grind_close`, accepts fallback `by grind` on `second_eqsat`
    // - Rejects all candidates on `third_unslimmable`
    const mockVerifier = async (candidateContent) => {
      if (candidateContent.includes("by eqsat_rw") || candidateContent.includes("by grind_close")) {
        return { ok: false, errorCount: 1, warningCount: 0, firstIssue: "eqsat_rw/grind_close failed to close goal" };
      }
      if (
        candidateContent.includes("by finset_nonneg") ||
        candidateContent.includes("by matrix_pos") ||
        candidateContent.includes("by convex_comb") ||
        candidateContent.includes("by positivity")
      ) {
        return { ok: false, errorCount: 1, warningCount: 0, firstIssue: "unsolved goals" };
      }
      if (candidateContent.includes("by sum_congr_ring") && !candidateContent.includes("import MyProject.Tactics")) {
        return { ok: false, errorCount: 1, warningCount: 0, firstIssue: "unknown tactic 'sum_congr_ring'" };
      }
      return { ok: true, errorCount: 0, warningCount: 0 };
    };

    // 1. Dry-run: must NOT mutate disk
    const dryReport = await runKernelVerifiedAutoSlim(tmpDir, {
      filePath: leanFile,
      apply: false,
      mode: "lsp",
      allowAltProofImport: true,
      lspVerifier: mockVerifier,
    });
    assert.equal(dryReport.applied, false);
    assert.equal(dryReport.dryRun, true);
    assert.equal(dryReport.importInserted, true);
    assert.equal(dryReport.verifiedCount, 2);
    assert.equal(dryReport.rejectedCount, 1);
    assert.equal(dryReport.edits[0].theoremName, "first_sum");
    assert.equal(dryReport.edits[0].newText, "by sum_congr_ring");
    assert.equal(dryReport.edits[1].theoremName, "second_eqsat");
    assert.equal(dryReport.edits[1].newText, "by grind");
    assert.equal(fs.readFileSync(leanFile, "utf-8"), original, "Dry-run must never mutate disk");
    assert.ok(dryReport.netLinesSaved >= 5);

    // 2. Apply: atomically writes verified slimmed proofs + preserves unslimmable theorem intact
    const appliedReport = await runKernelVerifiedAutoSlim(tmpDir, {
      filePath: leanFile,
      apply: true,
      mode: "lsp",
      allowAltProofImport: true,
      lspVerifier: mockVerifier,
    });
    assert.equal(appliedReport.applied, true);
    const updated = fs.readFileSync(leanFile, "utf-8");
    assert.match(updated, /^import Mathlib\nimport MyProject\.Tactics\n/);
    assert.ok(updated.includes(":= by sum_congr_ring\n"));
    assert.ok(updated.includes(":= by grind\n"));
    assert.ok(updated.includes("exact sq_nonneg (f i)"), "Rejected theorem body must remain untouched");
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});

test("McpServer registers lean_autoslim + lean_metrics(action='autoslim') and CLI parser handles flags", async () => {
  assert.ok(TOOL_DEFINITIONS.some((t) => t.name === "lean_autoslim"));
  const parsedCli = parseAutoSlimCliArgs([
    "Foo/Bar.lean",
    "--apply",
    "--mode=lsp",
    "--allow-altproof-import",
    "--route=sum_congr_ring,finset_mono",
    "--max-candidates=12",
    "--markdown",
  ]);
  assert.equal(parsedCli.filePath, "Foo/Bar.lean");
  assert.equal(parsedCli.apply, true);
  assert.equal(parsedCli.mode, "lsp");
  assert.equal(parsedCli.allowAltProofImport, true);
  assert.deepEqual(parsedCli.routes, ["sum_congr_ring", "finset_mono"]);
  assert.equal(parsedCli.maxCandidates, 12);
  assert.equal(parsedCli.format, "markdown");

  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "autoslim-mcp-"));
  try {
    fs.writeFileSync(path.join(tmpDir, "lakefile.toml"), 'name = "demo"\n', "utf-8");
    const cleanLean = path.join(tmpDir, "Clean.lean");
    fs.writeFileSync(cleanLean, "theorem clean_ok (x : Nat) : x = x := by rfl\n", "utf-8");
    const srv = new McpServer(tmpDir);
    try {
      const jsonOut = await srv.executeTool("lean_autoslim", { filePath: "Clean.lean" });
      const rep = JSON.parse(jsonOut);
      assert.equal(rep.candidatesDiscovered, 0);
      assert.equal(rep.verifiedCount, 0);

      const mdOut = await srv.executeTool("lean_metrics", {
        action: "autoslim",
        target: "Clean.lean",
        format: "markdown",
      });
      assert.match(mdOut, /Auto-Slim Report/);
      assert.doesNotMatch(mdOut, /Kernel-Verified/);

      const cliBin = fileURLToPath(new URL("../bin/lean-autoslim.js", import.meta.url));
      const cliOut = execFileSync(process.execPath, [cliBin, cleanLean, "--markdown"], {
        encoding: "utf-8",
      });
      assert.match(cliOut, /Auto-Slim Report/);
    } finally {
      srv.dispose();
    }
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});
