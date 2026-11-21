// tests/test_axiom_audit_scope.mjs
// Verifies that lean_metrics(action="axiom_audit") reports source-text scan
// scope honestly without claiming transitive axiom-closure verification.
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { McpServer } from "../src/index.ts";

test("lean_axiom_audit JSON and Markdown report source-text-scan scope honestly", async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "axiom-audit-scope-"));
  try {
    const cleanFile = path.join(tmpDir, "Clean.lean");
    fs.writeFileSync(
      cleanFile,
      "import SomeUncheckedModule\n\ntheorem uses_imported : True := trivial\n",
      "utf-8"
    );

    const server = new McpServer(tmpDir);
    const jsonRaw = await server.executeTool("lean_metrics", {
      action: "axiom_audit",
      filePath: cleanFile,
      format: "json",
    });
    const parsed = JSON.parse(jsonRaw);
    assert.equal(parsed.clean, true);
    assert.equal(parsed.evidence_kind, "source-text-scan");
    assert.equal(parsed.transitive_axiom_closure_checked, false);
    assert.equal(parsed.gate_eligible, false);
    assert.match(parsed.verdict, /SOURCE SCAN CLEAR/);
    assert.match(parsed.scope_note, /lean_axiom_closure/);

    const mdRaw = await server.executeTool("lean_metrics", {
      action: "axiom_audit",
      filePath: cleanFile,
      format: "markdown",
    });
    assert.match(mdRaw, /# Lean Axiom Source Scan:/);
    assert.match(mdRaw, /SOURCE SCAN CLEAR/);
    assert.match(mdRaw, /transitive_axiom_closure_checked: false/);
    assert.match(mdRaw, /gate_eligible: false/);
    assert.ok(!mdRaw.includes("Formally closed system"));

    const dirtyFile = path.join(tmpDir, "Dirty.lean");
    fs.writeFileSync(
      dirtyFile,
      "axiom my_unproved_ax : False\ntheorem bad_thm : False := by sorry\n",
      "utf-8"
    );
    const dirtyJson = JSON.parse(
      await server.executeTool("lean_metrics", {
        action: "axiom_audit",
        filePath: dirtyFile,
        format: "json",
      })
    );
    assert.equal(dirtyJson.clean, false);
    assert.equal(dirtyJson.evidence_kind, "source-text-scan");
    assert.equal(dirtyJson.transitive_axiom_closure_checked, false);
    assert.equal(dirtyJson.gate_eligible, false);
    assert.equal(dirtyJson.custom_axioms.length, 1);
    assert.equal(dirtyJson.sorries.length, 1);
    assert.match(dirtyJson.verdict, /SOURCE SCAN FINDINGS/);
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});

test("lean_axiom_closure enforces kernel axiom ceiling [propext, Classical.choice, Quot.sound] and rejects Lean.ofReduceBool / sorryAx", async () => {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "axiom-closure-test-"));
  try {
    const server = new McpServer(tmpDir);

    // 1. Pass case: standard kernel axioms
    const passOut = "'MyTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]";
    const resPass = server.verifyKernelAxioms("MyTheorem", passOut);
    assert.match(resPass, /\[KERNEL AXIOM GATE PASSED\]/);
    assert.match(resPass, /propext, Classical.choice, Quot.sound/);

    // 2. Pass case: no axioms
    const noAxOut = "'MyTheorem' does not depend on any axioms";
    const resNoAx = server.verifyKernelAxioms("MyTheorem", noAxOut);
    assert.match(resNoAx, /\[KERNEL AXIOM GATE PASSED\]/);

    // 3. Reject case: Lean.ofReduceBool
    const ofReduceOut = "'MyTheorem' depends on axioms: [propext, Lean.ofReduceBool]";
    const resOfReduce = server.verifyKernelAxioms("MyTheorem", ofReduceOut);
    assert.match(resOfReduce, /\[KERNEL AXIOM GATE REJECTED\]/);
    assert.match(resOfReduce, /Lean\.ofReduceBool/);

    // 4. Reject case: sorryAx
    const sorryOut = "'MyTheorem' depends on axioms: [sorryAx]";
    const resSorry = server.verifyKernelAxioms("MyTheorem", sorryOut);
    assert.match(resSorry, /\[KERNEL AXIOM GATE REJECTED\]/);
    assert.match(resSorry, /sorryAx/);

    // 5. Reject case: uncertified axiom
    const customOut = "'MyTheorem' depends on axioms: [propext, MyCustomAxiom]";
    const resCustom = server.verifyKernelAxioms("MyTheorem", customOut);
    assert.match(resCustom, /\[KERNEL AXIOM GATE REJECTED\]/);
    assert.match(resCustom, /MyCustomAxiom/);

    // 6. timeoutMs validation/clamping on lean_axiom_closure (1000..300000)
    let capturedMax = null;
    let capturedTimeoutArg = null;
    server.runLeanStdin = async (_code, _ctx, timeoutArg, maxTimeout) => {
      capturedTimeoutArg = timeoutArg;
      capturedMax = maxTimeout;
      return "'Demo.thm' depends on axioms: [propext]";
    };
    const closed = await server.executeTool("lean_axiom_closure", {
      symbol: "Demo.thm",
      timeoutMs: 240000,
    });
    assert.equal(capturedTimeoutArg, 240000);
    assert.equal(capturedMax, 300000);
    assert.match(closed, /propext/);
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
});
