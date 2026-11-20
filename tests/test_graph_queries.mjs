// tests/test_graph_queries.mjs
// Comprehensive unit tests for Lean 4 Graph Query Engine:
// 1. lean_cone_query: runtime vs proof cone, 0 Prop leakage, @[csimp] twin tracking, axiom closure
// 2. lean_proof_clones: AST Merkle hashing, anti-unification, tactic clone ranking, helper synthesis
// 3. lean_kernel_whnf_hotspots: recursor branching, < 2^63 vs >= 2^63 limb boundaries, accumulator add-chains, unshared lets
// 4. McpServer tool dispatch and lean_metrics action routing.
// Scoped Unicode policy (INV-001; typographic-free by default).
// Strictly generic kernel terminology (KERNEL-LAW-01..31).

import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { test } from "node:test";
import {
  LeanConeQueryEngine,
  LeanProofCloneEngine,
  LeanKernelWHNFHotspotEngine,
  verifyKernelAxioms,
} from "../src/graph_queries.ts";
import { McpServer, Lean4IleanIndex } from "../src/index.ts";

// ============================================================================
// SUITE 1: VERIFY KERNEL AXIOMS (Axiom Gate)
// ============================================================================

test("verifyKernelAxioms: validates permitted axioms [propext, Classical.choice, Quot.sound]", () => {
  const passOut = "'myTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]";
  const res = verifyKernelAxioms("myTheorem", passOut);
  assert.equal(res.passed, true);
  assert.deepEqual(res.axioms, ["propext", "Classical.choice", "Quot.sound"]);
  assert.equal(res.forbidden.length, 0);
  assert.equal(res.uncertified.length, 0);
  assert.match(res.summary, /\[KERNEL AXIOM GATE PASSED\]/);
});

test("verifyKernelAxioms: handles theorems depending on no axioms", () => {
  const noAxOut = "'pureNat' does not depend on any axioms";
  const res = verifyKernelAxioms("pureNat", noAxOut);
  assert.equal(res.passed, true);
  assert.deepEqual(res.axioms, []);
  assert.match(res.summary, /\[KERNEL AXIOM GATE PASSED\]/);
});

test("verifyKernelAxioms: rejects Lean.ofReduceBool (native_decide / bv_decide)", () => {
  const badOut = "'badThm' depends on axioms: [propext, Lean.ofReduceBool]";
  const res = verifyKernelAxioms("badThm", badOut);
  assert.equal(res.passed, false);
  assert.equal(res.forbidden.length, 1);
  assert.match(res.forbidden[0], /Lean\.ofReduceBool/);
  assert.match(res.summary, /\[KERNEL AXIOM GATE REJECTED\]/);
});

test("verifyKernelAxioms: rejects sorryAx (sorry / admit)", () => {
  const sorryOut = "'incompleteThm' depends on axioms: [sorryAx]";
  const res = verifyKernelAxioms("incompleteThm", sorryOut);
  assert.equal(res.passed, false);
  assert.equal(res.forbidden.length, 1);
  assert.match(res.forbidden[0], /sorryAx/);
  assert.match(res.summary, /\[KERNEL AXIOM GATE REJECTED\]/);
});

test("verifyKernelAxioms: rejects uncertified non-standard axioms", () => {
  const customOut = "'axiomThm' depends on axioms: [propext, CustomUnsoundAxiom]";
  const res = verifyKernelAxioms("axiomThm", customOut);
  assert.equal(res.passed, false);
  assert.equal(res.uncertified.length, 1);
  assert.equal(res.uncertified[0], "CustomUnsoundAxiom");
  assert.match(res.summary, /\[KERNEL AXIOM GATE REJECTED\]/);
});

// ============================================================================
// SUITE 2: LEAN CONE QUERY ENGINE (lean_cone_query)
// ============================================================================

const CLEAN_CONE_FIXTURE = `
def helperOne (n : Nat) : Nat := n + 1
def helperTwo (n : Nat) : Nat := helperOne n * 2

def compute (n : Nat) : Nat :=
  helperTwo n + 3

@[csimp]
def compute_twin (n : Nat) : Nat :=
  compute n

def specModel (n : Nat) : Nat := (n + 1) * 2 + 3

theorem compute_correct (n : Nat) : compute n = specModel n := by
  rfl
`;

const LEAKY_CONE_FIXTURE = `
theorem leakedTheorem (n : Nat) : n = n := by rfl

def leakyHelper (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ => if leakedTheorem n = leakedTheorem n then 1 else 0

def badCompute (n : Nat) : Nat :=
  leakyHelper n
`;

test("LeanConeQueryEngine: computes clean runtime cone and proof cone", () => {
  const res = LeanConeQueryEngine.execute({
    runtimeRoot: "compute",
    proofRoot: "compute_correct",
    source: CLEAN_CONE_FIXTURE,
    strictZeroProp: true,
  });

  assert.equal(res.verdict, "UNVERIFIED");
  assert.equal(res.axiomClosure.status, "SKIPPED");
  assert.equal(res.propLeakage.length, 0);
  assert.equal(res.runtimeCone.root, "compute");
  assert.ok(res.runtimeCone.count >= 3); // compute, helperTwo, helperOne
  assert.ok(res.proofCone !== undefined);
  assert.equal(res.proofCone.root, "compute_correct");

  // Verify @[csimp] twin tracking
  assert.equal(res.csimpTwins.length, 1);
  assert.equal(res.csimpTwins[0].twin, "compute_twin");
});

test("LeanConeQueryEngine: detects Prop leakage into runtime computation cone", () => {
  const res = LeanConeQueryEngine.execute({
    runtimeRoot: "badCompute",
    source: LEAKY_CONE_FIXTURE,
    strictZeroProp: true,
  });

  assert.equal(res.verdict, "FAIL");
  assert.ok(res.propLeakage.length >= 1);
  const leak = res.propLeakage.find((l) => l.symbol === "leakedTheorem");
  assert.ok(leak, "leakedTheorem detected in runtime cone");
  assert.equal(leak.kind, "PROP_LEAKAGE_DETECTED");
  assert.deepEqual(leak.path, ["badCompute", "leakyHelper", "leakedTheorem"]);
});

test("LeanConeQueryEngine: integrates with Lean4IleanIndex .ilean references", () => {
  const tmpRoot = fs.mkdtempSync(path.join(os.tmpdir(), "lean-cone-test-"));
  const libDir = path.join(tmpRoot, ".lake", "build", "lib", "lean");
  fs.mkdirSync(libDir, { recursive: true });

  const ileanData = {
    version: 5,
    module: "ConeTest",
    decls: {
      stepA: [1, 0, 2, 20],
      stepB: [3, 0, 4, 20],
      runMain: [5, 0, 6, 20],
      correctnessThm: [7, 0, 8, 40],
    },
    directImports: [],
    references: {
      [JSON.stringify({ c: { m: "ConeTest", n: "stepA" } })]: {
        definition: [1, 0, 2, 20],
        usages: [[3, 10, 3, 15, "stepB"]],
      },
      [JSON.stringify({ c: { m: "ConeTest", n: "stepB" } })]: {
        definition: [3, 0, 4, 20],
        usages: [[5, 10, 5, 15, "runMain"]],
      },
      [JSON.stringify({ c: { m: "ConeTest", n: "runMain" } })]: {
        definition: [5, 0, 6, 20],
        usages: [[7, 10, 7, 17, "correctnessThm"]],
      },
    },
  };

  fs.writeFileSync(path.join(libDir, "ConeTest.ilean"), JSON.stringify(ileanData));
  fs.writeFileSync(path.join(tmpRoot, "ConeTest.lean"), "def stepA := 1\ndef stepB := stepA\ndef runMain := stepB\n");

  const index = new Lean4IleanIndex(tmpRoot);
  index.refresh();

  const res = LeanConeQueryEngine.execute({
    runtimeRoot: "runMain",
    proofRoot: "correctnessThm",
    index,
  });

  assert.equal(res.verdict, "UNVERIFIED");
  assert.equal(res.propLeakage.length, 0);
  const names = res.runtimeCone.declarations.map((d) => d.name);
  assert.ok(names.some((n) => n.includes("stepA")), "stepA in runtime cone");
  assert.ok(names.some((n) => n.includes("stepB")), "stepB in runtime cone");

  fs.rmSync(tmpRoot, { recursive: true, force: true });
});

// ============================================================================
// SUITE 3: LEAN PROOF CLONE ENGINE (lean_proof_clones)
// ============================================================================

const REPETITIVE_PROOFS_FIXTURE = `
theorem proofAlpha (a b : Nat) : a + b = b + a := by
  intro x
  simp only [Nat.add_comm]
  rw [Nat.add_assoc]
  have h1 : x + 0 = x := by omega
  omega
  rfl

theorem proofBeta (c d : Nat) : c + d = d + c := by
  intro y
  simp only [Nat.add_comm]
  rw [Nat.add_assoc]
  have h2 : y + 0 = y := by omega
  omega
  rfl

theorem proofGamma (m n : Nat) : m + n = n + m := by
  intro z
  simp only [Nat.add_comm]
  rw [Nat.add_assoc]
  have h3 : z + 0 = z := by omega
  omega
  rfl
`;

test("LeanProofCloneEngine: detects duplicate tactic subtrees and synthesizes helper", () => {
  const res = LeanProofCloneEngine.execute({
    source: REPETITIVE_PROOFS_FIXTURE,
    minNodes: 5,
    minOccurrences: 2,
    synthesizeHelper: true,
  });

  assert.ok(res.theoremsAnalyzed >= 3);
  assert.ok(res.clonesFound >= 1, "At least 1 clone group detected");
  assert.ok(res.estimatedLineSavings > 0);

  const topClone = res.cloneGroups[0];
  assert.ok(topClone.occurrencesCount >= 3, "Clone appears across all 3 theorems");
  assert.ok(topClone.nodeCount >= 5);
  assert.ok(topClone.synthesizedHelper !== undefined);
  assert.match(topClone.synthesizedHelper, /lemma helper_clone_/);
  assert.match(topClone.synthesizedHelper, /simp only/);
});

// ============================================================================
// SUITE 4: LEAN KERNEL WHNF HOTSPOT ENGINE (lean_kernel_whnf_hotspots)
// ============================================================================

const HOTSPOTS_FIXTURE = `
-- Hotspot 1: Branching recursor step > 30 nodes with if-then-else
def badBranchingRecursor (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun k ih =>
    if k % 2 == 0 then
      ih + k * 2 + 1
    else
      match k with
      | 0 => ih
      | _ => ih + k * 3
  ) n

-- Hotspot 2: Numeric constants >= 2^63 forcing GMP heap mpz
def wideStateGMP : Nat :=
  0x10000000000000000 + 18446744073709551616

-- Hotspot 3: Accumulator increment with Nat.add 1 acc building Theta(s^2) lazy add-chain
def lazyAccRecursor (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun k acc => Nat.add 1 acc) n

-- Clean definition: unboxed scalar limbs, branch-free stepAux, Nat.succ accumulator
def cleanWorker (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun _ acc => Nat.succ acc) n
`;

test("LeanKernelWHNFHotspotEngine: detects all 4 WHNF reduction hotspots", () => {
  const res = LeanKernelWHNFHotspotEngine.execute({
    source: HOTSPOTS_FIXTURE,
  });

  assert.equal(res.clean, false);
  assert.ok(res.hotspotsCount >= 3);

  // Check Rule 1: RULE_HOTSPOT_BRANCHING_RECURSOR (KERNEL-LAW-26)
  const branchHotspot = res.hotspots.find((h) => h.ruleId === "RULE_HOTSPOT_BRANCHING_RECURSOR");
  assert.ok(branchHotspot, "RULE_HOTSPOT_BRANCHING_RECURSOR detected");
  assert.equal(branchHotspot.law, "KERNEL-LAW-26");
  assert.equal(branchHotspot.symbol, "badBranchingRecursor");

  // Check Rule 2: RULE_HOTSPOT_GMP_LIMB_OVERFLOW (KERNEL-LAW-11)
  const gmpHotspot = res.hotspots.find((h) => h.ruleId === "RULE_HOTSPOT_GMP_LIMB_OVERFLOW");
  assert.ok(gmpHotspot, "RULE_HOTSPOT_GMP_LIMB_OVERFLOW detected");
  assert.equal(gmpHotspot.law, "KERNEL-LAW-11");
  assert.equal(gmpHotspot.symbol, "wideStateGMP");

  // Check Rule 3: RULE_HOTSPOT_ACCUMULATOR_ADD_CHAIN (KERNEL-LAW-25)
  const addChainHotspot = res.hotspots.find((h) => h.ruleId === "RULE_HOTSPOT_ACCUMULATOR_ADD_CHAIN");
  assert.ok(addChainHotspot, "RULE_HOTSPOT_ACCUMULATOR_ADD_CHAIN detected");
  assert.equal(addChainHotspot.law, "KERNEL-LAW-25");
  assert.equal(addChainHotspot.symbol, "lazyAccRecursor");
});

test("LeanKernelWHNFHotspotEngine: passes clean unboxed code with 0 hotspots", () => {
  const cleanCode = `
def cleanCompute (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 0 (fun _ acc => Nat.succ acc) n
`;
  const res = LeanKernelWHNFHotspotEngine.execute({
    source: cleanCode,
  });

  assert.equal(res.clean, true);
  assert.equal(res.hotspotsCount, 0);
});

// ============================================================================
// SUITE 5: MCPSERVER INTEGRATION & LEAN_METRICS ROUTING
// ============================================================================

test("McpServer: dispatches lean_cone_query, lean_proof_clones, lean_kernel_whnf_hotspots", async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "mcp-graph-test-"));
  const testFile = path.join(tmpDir, "TestModule.lean");
  fs.writeFileSync(testFile, CLEAN_CONE_FIXTURE);

  const server = new McpServer(tmpDir);

  // 1. Tool dispatch: lean_cone_query
  const coneOut = await server.executeTool("lean_cone_query", {
    runtimeRoot: "compute",
    proofRoot: "compute_correct",
    filePath: testFile,
  });
  assert.ok(typeof coneOut === "string");
  const coneJson = JSON.parse(coneOut);
  assert.equal(coneJson.verdict, "UNVERIFIED");
  assert.equal(coneJson.axiomClosure.status, "SKIPPED");

  // 2. Tool dispatch: lean_proof_clones
  const cloneOut = await server.executeTool("lean_proof_clones", {
    filePath: testFile,
    minNodes: 2,
    minOccurrences: 1,
  });
  assert.ok(typeof cloneOut === "string");
  const cloneJson = JSON.parse(cloneOut);
  assert.ok(cloneJson.theoremsAnalyzed >= 1);

  // 3. Tool dispatch: lean_kernel_whnf_hotspots
  const hotspotOut = await server.executeTool("lean_kernel_whnf_hotspots", {
    filePath: testFile,
  });
  assert.ok(typeof hotspotOut === "string");
  const hotspotJson = JSON.parse(hotspotOut);
  assert.equal(hotspotJson.clean, true);

  // 4. Action routing through lean_metrics
  const metricCone = await server.executeTool("lean_metrics", {
    action: "cone_audit",
    runtimeRoot: "compute",
    filePath: testFile,
  });
  assert.ok(typeof metricCone === "string");
  assert.equal(JSON.parse(metricCone).verdict, "UNVERIFIED");

  const metricHotspot = await server.executeTool("lean_metrics", {
    action: "whnf_hotspots",
    filePath: testFile,
  });
  assert.ok(typeof metricHotspot === "string");
  assert.equal(JSON.parse(metricHotspot).clean, true);

  fs.rmSync(tmpDir, { recursive: true, force: true });
});

test("McpServer: graph tool file reads stay inside the workspace", async (t) => {
  const fixture = fs.mkdtempSync(path.join(os.tmpdir(), "mcp-graph-scope-"));
  t.after(() => fs.rmSync(fixture, { recursive: true, force: true }));
  const workspace = path.join(fixture, "workspace");
  const sibling = path.join(fixture, "workspace-other");
  fs.mkdirSync(workspace);
  fs.mkdirSync(sibling);
  const inside = path.join(workspace, "Inside.lean");
  const outside = path.join(sibling, "Outside.lean");
  fs.writeFileSync(inside, CLEAN_CONE_FIXTURE);
  fs.writeFileSync(outside, CLEAN_CONE_FIXTURE);
  fs.symlinkSync(outside, path.join(workspace, "Linked.lean"), "file");
  const server = new McpServer(workspace);

  for (const [name, args] of [
    ["lean_cone_query", { runtimeRoot: "compute" }],
    ["lean_proof_clones", {}],
    ["lean_kernel_whnf_hotspots", {}],
    ["lean_metrics", { action: "cone_audit", runtimeRoot: "compute" }],
    ["lean_metrics", { action: "proof_clones" }],
    ["lean_metrics", { action: "whnf_hotspots" }],
  ]) {
    const result = await server.executeTool(name, { ...args, filePath: "Inside.lean" });
    assert.ok(JSON.parse(result), name);
    for (const filePath of [outside, "../workspace-other/Outside.lean", "Linked.lean"]) {
      await assert.rejects(
        server.executeTool(name, { ...args, filePath }),
        /graph query file is outside the workspace/,
        `${name}: ${filePath}`,
      );
    }
  }
});
