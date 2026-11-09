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
