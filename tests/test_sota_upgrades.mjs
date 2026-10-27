// tests/test_sota_upgrades.mjs
// Comprehensive SOTA Upgrades Test Suite for lean4-lsp-mcp:
//   - Question 2: lspRequestTimeoutMs (120000ms default + env override)
//   - Question 5 (Proposal 3): lean_multi_attempt (lsp / repl / pantograph + shiftBaselineKeys + goalShapeHash + col='both')
//   - Question 6 (Proposal 4A): Goedel-Prover-V2 <error> spans + APOLLO comment/string-safe sorrifyFailingLeafLines + solver cascade + Rule G-15
//   - Question 7 (Proposal 5): WASM single-source proof_fidelity_audit (OVER_CONCRETE_FIXED_ARITY, UNANNOTATED_COLLECTION_LITERAL, HAVE_SUBGOAL_NAT_TRUNCATION, SAIR) + lean_minimal_hypotheses + lean_profile_proof
//   - Question 8 (Proposal 6): lean_search (similar_proofs BM25 + lean-explore dep boost, workspace_symbols RRF, detail='summary')
//   - Questions 4a, 10, 12b: lean_skill_dispatch, lean_theorem_preflight, and Multi-Prover Router (.v / .thy)
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert";
import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
import {
  McpServer,
  lspRequestTimeoutMs,
  computeGoalShapeHash,
  shiftBaselineKeys,
  filterAttemptDiagnostics,
  buildAnnotatedErrorSpan,
  synthesizeApolloDiagnosticHint,
  tokenizeLeanCommentsAndStrings,
  sorrifyFailingLeafLines,
  REPAIR_SOLVER_CASCADE,
  synthesizeSubLemmaFromGoal,
  parseTheoremBindersForPruning,
  removeHypothesisFromHeader,
  retrieveSimilarProofsBM25,
  reciprocalRankFusion,
  auditLeanProofFidelity,
} from "../src/index.ts";

console.log("Running SOTA Upgrades Test Suite...");

// 1. Question 2: Cold-Start Timeout Fix (120000ms default + env override)
{
  const prev = process.env.LEAN_LSP_REQUEST_TIMEOUT_MS;
  delete process.env.LEAN_LSP_REQUEST_TIMEOUT_MS;
  assert.strictEqual(lspRequestTimeoutMs(), 120000, "default LSP request timeout is 120000ms");
  process.env.LEAN_LSP_REQUEST_TIMEOUT_MS = "180000";
  assert.strictEqual(lspRequestTimeoutMs(), 180000, "LEAN_LSP_REQUEST_TIMEOUT_MS overrides default");
  if (prev === undefined) delete process.env.LEAN_LSP_REQUEST_TIMEOUT_MS;
  else process.env.LEAN_LSP_REQUEST_TIMEOUT_MS = prev;
  console.log("  - Question 2 (lspRequestTimeoutMs): PASS");
}

// 2. Question 5: shiftBaselineKeys + filterAttemptDiagnostics + computeGoalShapeHash
{
  const baseline = [
    { line: 5, col: 1, severity: 1, message: "earlier error" },
    { line: 20, col: 3, severity: 1, message: "downstream error" },
  ];
  // Candidate tactic at line 10 expands by +2 lines (3-line snippet), shifting line 20 -> 22
  const current = [
    { line: 5, col: 1, severity: 1, message: "earlier error" },
    { line: 11, col: 5, severity: 1, message: "new tactic error inside snippet" },
    { line: 22, col: 3, severity: 1, message: "downstream error" },
  ];
  const shiftedKeys = shiftBaselineKeys(baseline, 10, 2);
  assert(shiftedKeys.has("22:3:1:downstream error"), "downstream error line shifted by +2");
  const filtered = filterAttemptDiagnostics(current, baseline, 10, 10, 2);
  assert.strictEqual(filtered.length, 1, "only new tactic error inside snippet window survives");
  assert.strictEqual(filtered[0].line, 11);

  const h1 = computeGoalShapeHash("```lean4\nx : Nat\n|- x = x\n```");
  const h2 = computeGoalShapeHash("x : Nat   |- x = x");
  assert.strictEqual(h1, h2, "goalShapeHash normalizes whitespace and fences");
  assert.strictEqual(computeGoalShapeHash("No active goals (proof complete)."), "SOLVED");
  console.log("  - Question 5 (shiftBaselineKeys & computeGoalShapeHash): PASS");
}

// 3. Question 6: Goedel-Prover-V2 <error> spans + APOLLO comment/string-safe sorrifyFailingLeafLines + Rule G-15
{
  const srcLines = [
    "theorem foo (a b : Nat) : a - b + b = a := by",
    "  omega",
  ];
  const span = buildAnnotatedErrorSpan(srcLines, 2, 3, 2, 8);
  assert.strictEqual(span, "2 |   <error>omega</error>", "Goedel-Prover-V2 <error> span rendered");
  const hint = synthesizeApolloDiagnosticHint("omega failed, unsolved goals", "a - b + b = a");
  assert(hint && hint.includes("APOLLO Nat.sub Truncation Hint"), "APOLLO Nat.sub hint synthesized");

  const trickyLean = [
    "-- line comment mentioning sorry and failing tactic",
    "/- outer block /* nested /- inner sorry -/ still comment -/",
    'def msg : String := "string with sorry inside"',
    "theorem broken (n : Nat) : n = n := by",
    "  have h : n = n := by ring_bad",
    "  linarith_bad -- preserve trailing comment",
  ].join("\n");

  const spans = tokenizeLeanCommentsAndStrings(trickyLean);
  assert(spans.some((s) => s.kind === "line_comment"), "detects line comment");
  assert(spans.some((s) => s.kind === "block_comment"), "detects nested block comment");
  assert(spans.some((s) => s.kind === "string"), "detects string literal");

  const { sorrifiedSource, replacedLines } = sorrifyFailingLeafLines(trickyLean, [1, 2, 3, 4, 5, 6]);
  assert.deepStrictEqual(replacedLines, [5, 6], "only leaf code tactic lines 5 and 6 are sorrified");
  assert(sorrifiedSource.includes("have h : n = n := by sorry"), "single-line have RHS sorrified");
  assert(sorrifiedSource.includes("  sorry -- preserve trailing comment"), "leaf tactic sorrified with trailing comment preserved");
  assert(sorrifiedSource.includes('def msg : String := "string with sorry inside"'), "string literal untouched");

  assert(!REPAIR_SOLVER_CASCADE.includes("native_decide"), "native_decide strictly excluded from solver cascade");
  const sub = synthesizeSubLemmaFromGoal("broken", 1, 6, "n : Nat\nh : n > 0\n|- n >= 1");
  assert.strictEqual(sub.name, "broken_subgoal_1");
  assert(sub.statement.includes("lemma broken_subgoal_1 (n : Nat) (h : n > 0) : n >= 1"));
  assert.strictEqual(sub.revertingMacro, "p2m_exact_reverting broken_subgoal_1");
  console.log("  - Question 6 (Goedel <error>, APOLLO lexer sorrifier, solver cascade, Rule G-15): PASS");
}

// 4. Question 7: Grouped-binder hypothesis pruning + WASM single-source proof_fidelity_audit
{
  const hdr = "theorem grouped_test (x : Nat) (h1 h2 : x > 0) (h3 : x < 10) : x > 0";
  const slots = parseTheoremBindersForPruning(hdr);
  assert.strictEqual(slots.length, 4, "parses 4 binder variables across grouped binders");
  const pruned1 = removeHypothesisFromHeader(hdr, "h1");
  assert(pruned1.includes("(h2 : x > 0)"), "removing h1 from (h1 h2 : x > 0) preserves sibling h2");
  assert(!pruned1.includes("h1"), "h1 removed");
  const pruned2 = removeHypothesisFromHeader(pruned1, "h3");
  assert(!pruned2.includes("h3"), "single binder h3 removed cleanly");

  const fidelitySrc = [
    "theorem concrete_vec (x1 x2 x3 x4 : Nat) : x1 = x1 := by",
    "  have h_coll := {x1, x2}",
    "  have h_trunc : x1 - 3 = 2 := by omega",
    "  rfl",
  ].join("\n");
  const fidReport = auditLeanProofFidelity(fidelitySrc);
  const kinds = new Set(fidReport.diagnostics.map((d) => d.kind));
  assert(kinds.has("OVER_CONCRETE_FIXED_ARITY"), "detects OVER_CONCRETE_FIXED_ARITY");
  assert(kinds.has("UNANNOTATED_COLLECTION_LITERAL"), "detects UNANNOTATED_COLLECTION_LITERAL");
  assert(kinds.has("HAVE_SUBGOAL_NAT_TRUNCATION"), "detects HAVE_SUBGOAL_NAT_TRUNCATION");
  assert(Array.isArray(fidReport.wasmDiagnostics), "exposes WASM single-source diagnostics array");
  assert(Array.isArray(fidReport.sairDiagnostics), "exposes SAIR 37-Law diagnostics array");
  console.log("  - Question 7 (grouped-binder pruning & WASM single-source proof_fidelity_audit): PASS");
}

// 5. Question 8: Rango/CoqPilot BM25 similar_proofs + Reciprocal Rank Fusion
{
  const files = [
    {
      filePath: "Math/Simplex.lean",
      content: [
        "theorem simplex_nonneg (x : Nat) (h : x > 0) : x >= 1 := by",
        "  omega",
        "",
        "theorem simplex_sum_bound (x y : Nat) (hx : x > 0) : x + y >= 1 := by",
        "  have h1 := simplex_nonneg x hx",
        "  omega",
      ].join("\n"),
    },
  ];
  const sim = retrieveSimilarProofsBM25("simplex_nonneg x > 0 omega", files, 5);
  assert(sim.length >= 2, "retrieves similar proofs via BM25");
  assert.strictEqual(sim[0].theoremName, "simplex_nonneg", "top match is simplex_nonneg (boosted by in-pool dependency)");

  const rrf = reciprocalRankFusion(
    [
      [{ id: "A" }, { id: "B" }],
      [{ id: "B" }, { id: "C" }],
    ],
    60
  );
  assert.strictEqual(rrf[0].item.id, "B", "B ranks #1 under Reciprocal Rank Fusion across both lists");
  console.log("  - Question 8 (similar_proofs BM25 & Reciprocal Rank Fusion): PASS");
}

// 6. End-to-End McpServer SOTA Tool Execution
{
  process.env.LEAN_SKIP_LSP_FOR_TEST = "1";
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "lean-sota-test-"));
  const sampleLean = path.join(tmpDir, "Sample.lean");
  fs.writeFileSync(
    sampleLean,
    [
      "theorem sample_thm (a b : Nat) (h1 h2 : a > 0) (h_unused : b > 0) : a >= 1 := by",
      "  have h_step : a >= 1 := by omega",
      "  sorry",
    ].join("\n"),
    "utf-8"
  );

  try {
    const server = new McpServer(tmpDir);

    // 6a. lean_goal with col: 'both'
    const goalBothRaw = await server.executeTool("lean_goal", {
      filePath: sampleLean,
      line: 2,
      col: "both",
    });
    const goalBoth = JSON.parse(goalBothRaw);
    assert(goalBoth.goals_before && goalBoth.goals_after, "col=both returns goals_before and goals_after");
    assert(goalBoth.goal_shape_hash_before && goalBoth.goal_shape_hash_after, "col=both returns goal shape hashes");

    // 6b. lean_multi_attempt across lsp, repl, pantograph + multi-prover (.v, .thy)
    for (const mode of ["lsp", "repl", "pantograph"]) {
      const maRaw = await server.executeTool("lean_multi_attempt", {
        filePath: sampleLean,
        line: 3,
        snippets: ["skip", "omega"],
        mode,
      });
      const ma = JSON.parse(maRaw);
      assert.strictEqual(ma.diskMutated, false, "lean_multi_attempt never mutates disk");
      assert.strictEqual(ma.attemptCount, 2);
      assert.strictEqual(ma.results[0].noOp, true, "skip detected as noOp via goalShapeHash");
      assert.strictEqual(ma.results[1].solved, true, "omega detected as solved");
    }

    const coqRoute = JSON.parse(
      await server.executeTool("lean_multi_attempt", {
        filePath: "Test.v",
        line: 10,
        snippets: ["auto.", "lia."],
      })
    );
    assert.strictEqual(coqRoute.prover, "rocq-coq");
    assert.strictEqual(coqRoute.results.length, 2);

    const isaRoute = JSON.parse(
      await server.executeTool("lean_goal", {
        filePath: "Theory.thy",
        line: 5,
      })
    );
    assert.strictEqual(isaRoute.prover, "isabelle-hol");

    // 6c. lean_repair_proof
    const rep = JSON.parse(
      await server.executeTool("lean_repair_proof", {
        filePath: sampleLean,
        theoremName: "sample_thm",
        errorLines: [3],
      })
    );
    assert.strictEqual(rep.nativeDecideExcluded, true);
    assert(rep.branchRepairs.length >= 1);

    // 6d. lean_minimal_hypotheses
    const minHyp = JSON.parse(
      await server.executeTool("lean_minimal_hypotheses", {
        filePath: sampleLean,
        theoremName: "sample_thm",
      })
    );
    assert(minHyp.unusedHypotheses.includes("h_unused"), "detects unused hypothesis h_unused");
    assert(!minHyp.prunedHeader.includes("h_unused"), "prunes h_unused from header");

    // 6e. lean_profile_proof
    const prof = JSON.parse(
      await server.executeTool("lean_profile_proof", {
        filePath: sampleLean,
        theoremName: "sample_thm",
      })
    );
    assert(prof.totalTacticStepsProfiled >= 1);

    // 6f. lean_skill_dispatch
    const skill = JSON.parse(
      await server.executeTool("lean_skill_dispatch", {
        skillOrQuery: "lean-proof",
        role: "prover",
      })
    );
    assert.strictEqual(skill.role, "prover");
    assert(skill.allowedTools.includes("lean_multi_attempt"));

    // 6g. lean_theorem_preflight
    const preflight = JSON.parse(
      await server.executeTool("lean_theorem_preflight", {
        filePath: sampleLean,
        theoremName: "sample_thm",
        skipCounterexample: true,
      })
    );
    assert.strictEqual(preflight.theoremName, "sample_thm");
    assert(preflight.altProofAdvisor);

    // 6h. lean_search with source='similar_proofs' and detail='summary'
    const simSummary = await server.executeTool("lean_search", {
      query: "sample_thm Nat omega",
      source: "similar_proofs",
      filePath: sampleLean,
      detail: "summary",
    });
    assert(typeof simSummary === "string");

    console.log("  - End-to-End McpServer SOTA Tools (6 tools + hybrid search + multi-prover): PASS");
  } finally {
    delete process.env.LEAN_SKIP_LSP_FOR_TEST;
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
}

console.log("All SOTA Upgrades tests PASSED!");
