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
import {
  buildCandidateTacticList,
  computeUtf16LineOffsets,
  detectAltProofAvailability,
  discoverAutoSlimCandidates,
  lspRangeToStringOffsets,
  runKernelVerifiedAutoSlim,
} from "../src/autoslim.ts";
import { McpServer, TOOL_DEFINITIONS } from "../src/index.ts";
import { parseAutoSlimCliArgs } from "../bin/lean-autoslim.js";

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
      if (candidateContent.includes("by finset_nonneg") || candidateContent.includes("by positivity")) {
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
      assert.match(mdOut, /Kernel-Verified Auto-Slim Report/);

      const cliBin = fileURLToPath(new URL("../bin/lean-autoslim.js", import.meta.url));
      const cliOut = execFileSync(process.execPath, [cliBin, cleanLean, "--markdown"], {
        encoding: "utf-8",
      });
      assert.match(cliOut, /Kernel-Verified Auto-Slim Report/);
    } finally {
      srv.dispose();
    }
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});
