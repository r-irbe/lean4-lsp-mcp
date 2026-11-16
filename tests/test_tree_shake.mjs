// tests/test_tree_shake.mjs
// Unit and end-to-end tests for Lean 4 declaration/module tree-shaking (`lean_tree_shake` + CLI)
// and `.ilean` namespace-prefixed reference normalization.
// Scoped Unicode policy (INV-001; strict 7-bit ASCII source).

import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { test } from "node:test";
import { Lean4IleanIndex, McpServer, TOOL_DEFINITIONS } from "../src/index.ts";
import {
  anonymizeLeanSource,
  normalizeQualifiedDeclId,
  rewriteModuleImports,
  runLeanTreeShake,
  scanDirectoryForIdentityLeaks,
} from "../src/tree_shake.ts";
import { parseTreeShakeCliArgs } from "../bin/lean-tree-shake.js";

test("Lean4IleanIndex does not double-prefix already namespace-qualified .ilean references", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "ilean-nsprefix-"));
  try {
    const libDir = path.join(root, ".lake", "build", "lib", "lean", "MyPkg");
    fs.mkdirSync(libDir, { recursive: true });
    fs.mkdirSync(path.join(root, "MyPkg"), { recursive: true });
    fs.writeFileSync(path.join(root, "lakefile.toml"), 'name = "MyPkg"\n', "utf-8");
    fs.writeFileSync(
      path.join(root, "MyPkg", "Opinion.lean"),
      "namespace MyPkg.Opinion\ndef wbf : Nat := 1\ntheorem use_wbf : wbf = 1 := rfl\nend MyPkg.Opinion\n",
      "utf-8"
    );
    const ilean = {
      version: 5,
      module: "MyPkg.Opinion",
      decls: {
        "MyPkg.Opinion.wbf": [1, 0, 1, 18],
        "MyPkg.Opinion.use_wbf": [2, 0, 2, 33],
      },
      directImports: [["Init", false, false, false]],
      references: {
        [JSON.stringify({ c: { m: "MyPkg.Opinion", n: "MyPkg.Opinion.wbf" } })]: {
          definition: [1, 0, 1, 18],
          usages: [[2, 18, 2, 21, "MyPkg.Opinion.use_wbf"]],
        },
        [JSON.stringify({ c: { m: "MyPkg.Opinion", n: "MyPkg.BinomialOpinion" } })]: {
          definition: [1, 0, 1, 18],
          usages: [[2, 18, 2, 21, "MyPkg.Opinion.use_wbf"]],
        },
      },
    };
    fs.writeFileSync(path.join(libDir, "Opinion.ilean"), JSON.stringify(ilean), "utf-8");

    const idx = new Lean4IleanIndex(root);
    idx.refresh();
    const uses = idx.lookupReferences("MyPkg.Opinion.use_wbf", "uses", 20);
    assert.equal(uses.resolved, true);
    const joined = uses.lines.join("\n");
    assert.ok(joined.includes("MyPkg.Opinion.wbf"), `Expected MyPkg.Opinion.wbf, got:\n${joined}`);
    assert.ok(joined.includes("MyPkg.BinomialOpinion"), `Expected MyPkg.BinomialOpinion, got:\n${joined}`);
    assert.ok(
      !joined.includes("MyPkg.Opinion.MyPkg."),
      `Must not duplicate module/package prefix, got:\n${joined}`
    );

    const usedBy = idx.lookupReferences("MyPkg.Opinion.wbf", "usedBy", 20);
    assert.equal(usedBy.resolved, true);
    assert.ok(usedBy.lines.join("\n").includes("MyPkg.Opinion.use_wbf"));
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("runLeanTreeShake drops unused hub imports, promotes transitive dependencies, prunes dead theorems, and anonymizes", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "treeshake-proj-"));
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), "treeshake-out-"));
  try {
    fs.writeFileSync(path.join(root, "lean-toolchain"), "v4.34.1\n", "utf-8");
    fs.writeFileSync(
      path.join(root, "lakefile.lean"),
      'import Lake\nopen Lake DSL\npackage DemoPkg where\nlean_lib DemoPkg where\n  srcDir := "."\n',
      "utf-8"
    );
    fs.writeFileSync(
      path.join(root, "lake-manifest.json"),
      JSON.stringify({ version: "1.2.0", name: "DemoPkg", packagesDir: ".lake/packages", packages: [] }, null, 2),
      "utf-8"
    );

    const srcDir = path.join(root, "DemoPkg");
    const libDir = path.join(root, ".lake", "build", "lib", "lean", "DemoPkg");
    fs.mkdirSync(srcDir, { recursive: true });
    fs.mkdirSync(libDir, { recursive: true });

    // Leaf.lean: defines `used_leaf` and `dead_leaf` (with multi-byte math comment)
    const leafSrc = [
      "/-",
      "Copyright (c) 2026 SecretAuthor (https://github.com/secret-user/secret-repo)",
      "Authors: SecretAuthor",
      "-/",
      "namespace DemoPkg.Leaf",
      "",
      "def used_leaf : Nat := 42",
      "",
      "/-- Dead theorem over \u2115 that should be tree-shaken away. -/",
      "theorem dead_leaf : 1 + 1 = 2 := by",
      "  rfl",
      "",
      "end DemoPkg.Leaf",
      "",
    ].join("\n");
    fs.writeFileSync(path.join(srcDir, "Leaf.lean"), leafSrc, "utf-8");

    // DeadHub.lean: imports Leaf, defines only unused `dead_hub_thm`
    const hubSrc = [
      "import DemoPkg.Leaf",
      "namespace DemoPkg.DeadHub",
      "theorem dead_hub_thm : DemoPkg.Leaf.used_leaf = 42 := rfl",
      "end DemoPkg.DeadHub",
      "",
    ].join("\n");
    fs.writeFileSync(path.join(srcDir, "DeadHub.lean"), hubSrc, "utf-8");

    // UnusedSibling.lean: completely unused module
    fs.writeFileSync(
      path.join(srcDir, "UnusedSibling.lean"),
      "namespace DemoPkg.UnusedSibling\ntheorem giant_unused : True := trivial\nend DemoPkg.UnusedSibling\n",
      "utf-8"
    );

    // Entry.lean: imports DeadHub (getting Leaf transitively!) and UnusedSibling, uses ONLY `DemoPkg.Leaf.used_leaf`
    const entrySrc = [
      "import DemoPkg.DeadHub",
      "import DemoPkg.UnusedSibling",
      "",
      "namespace DemoPkg.Entry",
      "#check @DemoPkg.Leaf.used_leaf",
      "theorem entry_main : DemoPkg.Leaf.used_leaf = 42 := rfl",
      "end DemoPkg.Entry",
      "",
    ].join("\n");
    fs.writeFileSync(path.join(srcDir, "Entry.lean"), entrySrc, "utf-8");

    // Emit corresponding `.ilean` files
    fs.writeFileSync(
      path.join(libDir, "Leaf.ilean"),
      JSON.stringify({
        version: 5,
        module: "DemoPkg.Leaf",
        directImports: [["Init", false, false, false]],
        decls: {
          "DemoPkg.Leaf.used_leaf": [6, 0, 6, 25],
          "DemoPkg.Leaf.dead_leaf": [8, 0, 10, 5],
        },
        references: {},
      }),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(libDir, "DeadHub.ilean"),
      JSON.stringify({
        version: 5,
        module: "DemoPkg.DeadHub",
        directImports: [["DemoPkg.Leaf", false, false, false]],
        decls: { "DemoPkg.DeadHub.dead_hub_thm": [2, 0, 2, 56] },
        references: {
          [JSON.stringify({ c: { m: "DemoPkg.Leaf", n: "DemoPkg.Leaf.used_leaf" } })]: {
            definition: null,
            usages: [[2, 23, 2, 45, "DemoPkg.DeadHub.dead_hub_thm"]],
          },
        },
      }),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(libDir, "UnusedSibling.ilean"),
      JSON.stringify({
        version: 5,
        module: "DemoPkg.UnusedSibling",
        directImports: [["Init", false, false, false]],
        decls: { "DemoPkg.UnusedSibling.giant_unused": [1, 0, 1, 40] },
        references: {},
      }),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(libDir, "Entry.ilean"),
      JSON.stringify({
        version: 5,
        module: "DemoPkg.Entry",
        directImports: [
          ["DemoPkg.DeadHub", false, false, false],
          ["DemoPkg.UnusedSibling", false, false, false],
        ],
        decls: { "DemoPkg.Entry.entry_main": [5, 0, 5, 55] },
        references: {
          [JSON.stringify({ c: { m: "DemoPkg.Leaf", n: "DemoPkg.Leaf.used_leaf" } })]: {
            definition: null,
            usages: [
              [4, 8, 4, 30, "_check"],
              [5, 21, 5, 43, "DemoPkg.Entry.entry_main"],
            ],
          },
        },
      }),
      "utf-8"
    );

    const archivePath = path.join(outDir, "anon.tar.gz");
    const sliceDir = path.join(outDir, "slice");
    const report = await runLeanTreeShake({
      projectRoot: root,
      entryModules: ["DemoPkg.Entry"],
      outputDir: sliceDir,
      archivePath,
      granularity: "declaration",
      anonymize: true,
      forbiddenPatterns: ["SecretAuthor", "secret-user", "secret-repo"],
    });

    assert.equal(report.totalCorpusModules, 4);
    assert.equal(report.fileImportClosureModules, 4);
    assert.equal(report.keptModulesCount, 2, "Only Entry and Leaf should remain");
    assert.equal(report.anonymityLeakHits.length, 0, "Zero anonymity leaks");
    assert.ok(fs.existsSync(archivePath), "Archive created");
    assert.ok(!fs.existsSync(path.join(sliceDir, "DemoPkg", "DeadHub.lean")));
    assert.ok(!fs.existsSync(path.join(sliceDir, "DemoPkg", "UnusedSibling.lean")));

    const emittedEntry = fs.readFileSync(path.join(sliceDir, "DemoPkg", "Entry.lean"), "utf-8");
    assert.ok(
      emittedEntry.includes("import DemoPkg.Leaf"),
      `Transitive dependency Leaf must be promoted when DeadHub is dropped:\n${emittedEntry}`
    );
    assert.ok(!emittedEntry.includes("DeadHub"));
    assert.ok(!emittedEntry.includes("UnusedSibling"));

    const emittedLeaf = fs.readFileSync(path.join(sliceDir, "DemoPkg", "Leaf.lean"), "utf-8");
    assert.ok(emittedLeaf.includes("def used_leaf"), "Reachable def preserved");
    assert.ok(!emittedLeaf.includes("dead_leaf"), `Dead theorem pruned:\n${emittedLeaf}`);
    assert.ok(!emittedLeaf.includes("SecretAuthor"), "Author header scrubbed");

    // Verify MCP server wiring (`lean_tree_shake` + `lean_metrics` action='tree_shake')
    assert.ok(TOOL_DEFINITIONS.some((t) => t.name === "lean_tree_shake"));
    const server = new McpServer(root);
    const mcpJson = JSON.parse(
      await server.executeTool("lean_tree_shake", {
        entryModules: ["DemoPkg.Entry"],
        granularity: "declaration",
      })
    );
    assert.equal(mcpJson.keptModulesCount, 2);

    const metricsMd = await server.executeTool("lean_metrics", {
      action: "tree_shake",
      target: "DemoPkg.Entry",
      format: "markdown",
    });
    assert.ok(metricsMd.includes("Lean 4 Tree-Shake Report"));
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
    fs.rmSync(outDir, { recursive: true, force: true });
  }
});

test("CLI parser and helper utilities handle flags accurately", () => {
  assert.equal(normalizeQualifiedDeclId("A.B", "A.B.foo"), "A.B.foo");
  assert.equal(normalizeQualifiedDeclId("A.B", "foo"), "A.B.foo");
  assert.equal(normalizeQualifiedDeclId("A.B", "A.B"), "A.B");

  const anon = anonymizeLeanSource(
    "/-\nCopyright (c) 2026 Alice\nAuthors: Alice\n-/\n-- see https://github.com/alice/private-repo\ndef x := 1\n"
  );
  assert.ok(!anon.includes("Alice"));
  assert.ok(!anon.includes("alice/private-repo"));

  const rewritten = rewriteModuleImports(
    "import Mathlib.Data.Nat.Basic\nimport Pkg.Dead\nimport Pkg.Kept\n",
    (m) => m.startsWith("Pkg."),
    new Set(["Pkg.Kept"]),
    ["Pkg.Promoted"]
  );
  assert.equal(rewritten, "import Mathlib.Data.Nat.Basic\nimport Pkg.Kept\nimport Pkg.Promoted\n");

  const parsed = parseTreeShakeCliArgs([
    "MyProject.Synthesis.Concordance",
    "--anonymize",
    "--verify-build",
    "--granularity=declaration",
    "--forbid",
    "alice,bob",
    "--markdown",
  ]);
  assert.deepEqual(parsed.entryModules, ["MyProject.Synthesis.Concordance"]);
  assert.equal(parsed.anonymize, true);
  assert.equal(parsed.verifyBuild, true);
  assert.equal(parsed.granularity, "declaration");
  assert.deepEqual(parsed.forbiddenPatterns, ["alice", "bob"]);
  assert.equal(parsed.format, "markdown");

  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "leak-scan-"));
  try {
    fs.writeFileSync(path.join(tmp, "A.lean"), "-- clean file\n", "utf-8");
    assert.equal(scanDirectoryForIdentityLeaks(tmp, ["SecretName"]).length, 0);
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});
