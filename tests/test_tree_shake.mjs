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
  analyzeModuleSyntax,
  anonymizeLeanSource,
  codeContainsSurfaceKeyword,
  normalizeQualifiedDeclId,
  pruneModuleDeclarations,
  rewriteModuleImports,
  runLeanTreeShake,
  scanDirectoryForIdentityLeaks,
  stripOrphanSectionHusks,
  stripUnusedSyntaxBlocks,
  synthesizeSliceModuleDocstring,
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

test("stripOrphanSectionHusks, @[deprecated] pruning, dead carrier @[simp]/instance pruning, and third-party URL preservation", () => {
  // 1. Third-party upstream attribution URLs (`Vilin97`, `harfe`) stay intact while private URLs are scrubbed
  const anonUrls = anonymizeLeanSource(
    "-- Ported from https://github.com/Vilin97/lean-pool and https://github.com/harfe/fixed-point-theorems-lean4\n-- Internal: https://github.com/myorg/secret-repo\n"
  );
  assert.ok(anonUrls.includes("https://github.com/Vilin97/lean-pool"));
  assert.ok(anonUrls.includes("https://github.com/harfe/fixed-point-theorems-lean4"));
  assert.ok(!anonUrls.includes("myorg/secret-repo"));

  // 2. Empty `namespace ... end` shells and stacked/trailing `/-! ... -/` + `-- ====` husks are stripped
  const husky = [
    "/-! # Primary Module Docstring -/",
    "",
    "namespace Demo",
    "",
    "-- ============================================================",
    "-- Part I: Completely Pruned Section",
    "-- ============================================================",
    "/-! ## Section 1 (pruned) -/",
    "",
    "namespace DeadSub",
    "/-! ### Dead inner notes -/",
    "end DeadSub",
    "",
    "-- ============================================================",
    "-- Part II: Live Section",
    "-- ============================================================",
    "/-! ## Section 2 (kept) -/",
    "def keptVal : Nat := 7",
    "",
    "-- ============================================================",
    "-- Part III: Trailing Husk",
    "-- ============================================================",
    "/-! ## Section 3 (pruned trailer) -/",
    "",
    "end Demo",
    "",
  ].join("\n");
  const deHusked = stripOrphanSectionHusks(husky);
  assert.ok(deHusked.includes("Primary Module Docstring"), "Primary module docstring preserved");
  assert.ok(deHusked.includes("Part II: Live Section"), "Immediately preceding banner preserved");
  assert.ok(deHusked.includes("Section 2 (kept)"), "Immediately preceding section docstring preserved");
  assert.ok(deHusked.includes("def keptVal : Nat := 7"), "Live code preserved");
  assert.ok(!deHusked.includes("Part I:"), `Stacked pruned banner stripped:\n${deHusked}`);
  assert.ok(!deHusked.includes("Section 1 (pruned)"), `Stacked pruned sectionDoc stripped:\n${deHusked}`);
  assert.ok(!deHusked.includes("DeadSub"), `Empty namespace shell stripped:\n${deHusked}`);
  assert.ok(!deHusked.includes("Part III:"), `Trailing banner stripped:\n${deHusked}`);
  assert.ok(!deHusked.includes("Section 3"), `Trailing sectionDoc stripped:\n${deHusked}`);

  // 3. `@[deprecated]` aliases, `@[simp]`/`instance` on unreferenced local carriers, and dangling `see \`PrunedDecl\`` clauses are pruned
  const modSrc = [
    "/-- Live function (Bool-valued; see `deadFn` for the Prop-valued version). -/",
    "def liveFn (n : Nat) : Nat := n + 1",
    "@[simp] theorem liveFn_zero : liveFn 0 = 1 := rfl",
    "@[deprecated liveFn (since := \"2026-11-16\")] abbrev legacyFn := liveFn",
    "def deadFn (n : Nat) : Nat := n + 2",
    "@[simp] theorem deadFn_zero : deadFn 0 = 2 := rfl",
    "class DeadClass (a : Type) where",
    "  val : a",
    "instance instDeadNat : DeadClass Nat where",
    "  val := 0",
  ].join("\n");
  const ileanDecls = {
    liveFn: [0, 0, 1, 35, 1, 4, 1, 10],
    liveFn_zero: [2, 0, 2, 49, 2, 16, 2, 27],
    legacyFn: [3, 0, 3, 71, 3, 52, 3, 60],
    deadFn: [4, 0, 4, 35, 4, 4, 4, 10],
    deadFn_zero: [5, 0, 5, 49, 5, 16, 5, 27],
    DeadClass: [6, 0, 7, 10, 6, 6, 6, 15],
    instDeadNat: [8, 0, 9, 10, 8, 9, 8, 20],
  };
  const pruned = pruneModuleDeclarations(
    "/tmp/FakeMod.lean",
    modSrc,
    new Set(["liveFn"]),
    new Set(["liveFn"]),
    null,
    ileanDecls
  );
  assert.ok(pruned.prunedText.includes("def liveFn"), "liveFn kept");
  assert.ok(pruned.prunedText.includes("(Bool-valued)."), `Dangling '; see \`deadFn\`' clause scrubbed cleanly:\n${pruned.prunedText}`);
  assert.ok(!pruned.prunedText.includes("`deadFn`"), "Dangling pruned-decl doc cross-ref stripped");
  assert.ok(pruned.prunedText.includes("theorem liveFn_zero"), "@[simp] on liveFn kept");
  assert.ok(!pruned.prunedText.includes("legacyFn"), "@[deprecated] alias stripped");
  assert.ok(!pruned.prunedText.includes("deadFn"), "deadFn and its @[simp] lemma stripped");
  assert.ok(!pruned.prunedText.includes("DeadClass"), "unreferenced class stripped");
  assert.ok(!pruned.prunedText.includes("instDeadNat"), "instance of unreferenced class stripped");
});

test("surface-syntax-token tactic pruning and local path-package resolution prune unused macros & helpers", async () => {
  assert.equal(codeContainsSurfaceKeyword("by elegance?", "elegance?"), true);
  assert.equal(codeContainsSurfaceKeyword("by bfs_elegance?", "elegance?"), false);
  assert.equal(codeContainsSurfaceKeyword("let x := eval_nat% (2 + 3)", "eval_nat%"), true);
  assert.equal(codeContainsSurfaceKeyword("let x := eval_nat (2 + 3)", "eval_nat%"), false);
  assert.equal(codeContainsSurfaceKeyword("#p2m_type_eq foo bar", "#p2m_type_eq"), true);
  assert.equal(codeContainsSurfaceKeyword("#p2m_type_eq_warn foo bar", "#p2m_type_eq"), false);

  const tacSrc = [
    "/-- Used simp attr -/",
    "register_simp_attr dead_unfold",
    "",
    "/-- Live closer macro -/",
    'macro "live_closer" : tactic => `(tactic| exact rfl)',
    "",
    "/-- Dead closer macro -/",
    'syntax (name := deadTac) "dead_closer" : tactic',
    "@[tactic deadTac] def evalDeadTac : Unit := ()",
    "",
    "/-- Dead command generator -/",
    'syntax (name := genCmd) "gen_corollaries " ident : command',
    "macro_rules",
    "  | `(command| gen_corollaries $n:ident) => `(def $n := 0)",
    "",
    "gen_corollaries smoke_demo",
  ].join("\n");

  const analysis = analyzeModuleSyntax(tacSrc);
  assert.ok(analysis.allKeywords.has("live_closer"));
  assert.ok(analysis.allKeywords.has("dead_closer"));
  assert.ok(analysis.allKeywords.has("gen_corollaries"));
  assert.ok(analysis.allKeywords.has("dead_unfold"));
  assert.deepEqual(analysis.tacticAttrEvaluators.get("deadTac"), ["evalDeadTac"]);

  const strippedTac = stripUnusedSyntaxBlocks(tacSrc, new Set(["live_closer"]));
  assert.ok(strippedTac.includes("live_closer"), "active tactic macro retained");
  assert.ok(!strippedTac.includes("dead_closer"), "unused syntax stripped");
  assert.ok(!strippedTac.includes("gen_corollaries"), "unused command macro stripped");
  assert.ok(!strippedTac.includes("smoke_demo"), "column-0 smoke call of dropped command macro stripped");
  assert.ok(!strippedTac.includes("dead_unfold"), "unused register_simp_attr stripped");

  // End-to-end check with a local `"type": "path"` tactic package (`extpkg/TacPkg`)
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "shake-localpkg-"));
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), "shake-localpkg-out-"));
  try {
    const extRoot = path.join(root, "extpkg");
    fs.mkdirSync(path.join(root, "MainPkg"), { recursive: true });
    fs.mkdirSync(path.join(extRoot, "TacPkg"), { recursive: true });
    fs.mkdirSync(path.join(root, ".lake", "build", "lib", "lean", "MainPkg"), { recursive: true });
    fs.mkdirSync(path.join(extRoot, ".lake", "build", "lib", "lean", "TacPkg"), { recursive: true });

    fs.writeFileSync(path.join(root, "lean-toolchain"), "v4.34.1\n", "utf-8");
    fs.writeFileSync(
      path.join(root, "lake-manifest.json"),
      JSON.stringify(
        {
          version: "1.1.0",
          name: "MainPkg",
          packagesDir: ".lake/packages",
          packages: [
            { type: "path", name: "tacpkg", inherited: false, dir: "extpkg" },
            { type: "git", name: "mathlib", inherited: false, url: "https://github.com/leanprover-community/mathlib4.git", rev: "deadbeef", inputRev: "v4.34.1" },
          ],
        },
        null,
        2
      ) + "\n",
      "utf-8"
    );

    const closersLean = [
      'macro "used_tac" : tactic => `(tactic| rfl)',
      'macro "unused_tac" : tactic => `(tactic| exact deadHelper)',
      "def deadHelper : Nat := 99",
      "",
    ].join("\n");
    const coreLean = [
      'elab "elegance?" : tactic => pure ()',
      "def heavyMetaTable : Nat := 12345",
      "",
    ].join("\n");
    const umbrellaLean = "import TacPkg.Core\nimport TacPkg.Closers\n";
    const entryLean = [
      "import TacPkg",
      "theorem keep_thm : 1 = 1 := by used_tac",
      "",
    ].join("\n");

    fs.writeFileSync(path.join(extRoot, "TacPkg", "Closers.lean"), closersLean, "utf-8");
    fs.writeFileSync(path.join(extRoot, "TacPkg", "Core.lean"), coreLean, "utf-8");
    fs.writeFileSync(path.join(extRoot, "TacPkg.lean"), umbrellaLean, "utf-8");
    fs.writeFileSync(path.join(root, "MainPkg", "Entry.lean"), entryLean, "utf-8");

    fs.writeFileSync(
      path.join(extRoot, ".lake", "build", "lib", "lean", "TacPkg", "Closers.ilean"),
      JSON.stringify({
        module: "TacPkg.Closers",
        directImports: ["Init"],
        decls: { deadHelper: [2, 0, 2, 26, 2, 4, 2, 14] },
        references: {},
      }),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(extRoot, ".lake", "build", "lib", "lean", "TacPkg", "Core.ilean"),
      JSON.stringify({
        module: "TacPkg.Core",
        directImports: ["Init"],
        decls: { heavyMetaTable: [1, 0, 1, 33, 1, 4, 1, 18] },
        references: {},
      }),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(extRoot, ".lake", "build", "lib", "lean", "TacPkg.ilean"),
      JSON.stringify({
        module: "TacPkg",
        directImports: ["TacPkg.Core", "TacPkg.Closers"],
        decls: {},
        references: {},
      }),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(root, ".lake", "build", "lib", "lean", "MainPkg", "Entry.ilean"),
      JSON.stringify({
        module: "MainPkg.Entry",
        directImports: ["TacPkg"],
        decls: { keep_thm: [1, 0, 1, 39, 1, 8, 1, 16] },
        references: {},
      }),
      "utf-8"
    );

    const rep = await runLeanTreeShake({
      projectRoot: root,
      entryModules: ["MainPkg.Entry"],
      outputDir: outDir,
      anonymize: true,
      packageName: "AnonDemo",
    });

    assert.equal(rep.keptModulesCount, 2, "Only MainPkg.Entry and TacPkg.Closers should be kept");
    assert.ok(!fs.existsSync(path.join(outDir, "TacPkg", "Core.lean")), "Unused TacPkg.Core dropped completely");
    assert.ok(!fs.existsSync(path.join(outDir, "TacPkg.lean")), "Unused TacPkg umbrella dropped completely");
    const emittedClosers = fs.readFileSync(path.join(outDir, "TacPkg", "Closers.lean"), "utf-8");
    assert.ok(emittedClosers.includes("used_tac"), "used_tac retained");
    assert.ok(!emittedClosers.includes("unused_tac"), "unused_tac pruned");
    assert.ok(!emittedClosers.includes("deadHelper"), "deadHelper inside unused_tac pruned");
    const emittedEntry = fs.readFileSync(path.join(outDir, "MainPkg", "Entry.lean"), "utf-8");
    assert.ok(emittedEntry.includes("import TacPkg.Closers"), "TacPkg.Closers promoted directly into Entry.lean");
    assert.ok(!emittedEntry.includes("import TacPkg\n"), "Dropped TacPkg umbrella import removed");
    const emittedManifest = JSON.parse(fs.readFileSync(path.join(outDir, "lake-manifest.json"), "utf-8"));
    assert.equal(emittedManifest.packages.some((p) => p.name === "tacpkg"), false, "Inlined local path pkg removed from manifest");
    assert.equal(emittedManifest.packages.some((p) => p.name === "mathlib"), true, "External git pkg kept in manifest");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
    fs.rmSync(outDir, { recursive: true, force: true });
  }
});

test("anonymize mode prepends missing Apache-2.0 header, synthesizes accurate slice docstrings, scrubs backticked paths/wave tags without scars, and prunes unused git requires", async () => {
  const headerless = [
    "import Mathlib.Data.Nat.Basic",
    "/-! # Old Husk Docstring claiming `vanished_thm` and `docs/investigation-garden/secret.md` -/",
    "namespace Demo",
    "/-- (W57) Retained helper per `docs/refactor/wave-6/playbook.md` (HITL choice w28-c, REC-061) citing `Unshipped.lean:42`. -/",
    "def keptHelper : Nat := 1",
    "end Demo",
    "",
  ].join("\n");

  const anon = anonymizeLeanSource(headerless, {
    ensureLicenseHeader: true,
    keptModuleBaseNames: new Set(["Kept.lean"]),
    keptModuleNames: new Set(["Demo.Kept"]),
  });
  assert.ok(anon.startsWith("/-\nReleased under Apache 2.0 license."), `Missing header not prepended:\n${anon}`);
  assert.ok(!anon.includes("docs/refactor/"), `Mid-path scar leaked:\n${anon}`);
  assert.ok(!anon.includes("docs/investigation-garden/"), `Internal garden path leaked:\n${anon}`);
  assert.ok(!anon.includes("W57") && !anon.includes("HITL") && !anon.includes("REC-061"), `Campaign tags leaked:\n${anon}`);
  assert.ok(!anon.includes("Unshipped.lean"), `Unshipped .lean ref leaked:\n${anon}`);

  const docReplaced = synthesizeSliceModuleDocstring("Demo.Kept", ["keptHelper"], anon);
  assert.ok(docReplaced.includes("# Demo.Kept"), "Synthesized module title present");
  assert.ok(docReplaced.includes("`keptHelper`"), "Retained declaration listed");
  assert.ok(!docReplaced.includes("vanished_thm"), "Stale husk claim removed");

  // Multi-line `variable` inside empty namespace + trailing directive at EOF are stripped
  const multiVarHusk = [
    "/-! # Mod -/",
    "namespace DeadRealQ",
    "variable [Fintype Alpha]",
    "         [DecidableEq Alpha]",
    "end DeadRealQ",
    "def liveOne : Nat := 1",
    "open Classical",
    "variable {Omega : Type*}",
    "         {mu : Omega}",
    "",
  ].join("\n");
  const cleanedHusk = stripOrphanSectionHusks(multiVarHusk, { dropSectionDocs: true });
  assert.ok(!cleanedHusk.includes("DeadRealQ"), `Empty multi-line variable namespace survived:\n${cleanedHusk}`);
  assert.ok(!cleanedHusk.includes("Omega"), `Trailing multi-line variable survived:\n${cleanedHusk}`);
  assert.ok(cleanedHusk.includes("def liveOne : Nat := 1"));

  // End-to-end check that unused direct git require (`LSpec`) is pruned while used `mathlib` + `cslib` remain
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "treeshake-reqprune-"));
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), "treeshake-reqprune-out-"));
  try {
    fs.writeFileSync(path.join(root, "lean-toolchain"), "v4.34.1\n", "utf-8");
    fs.writeFileSync(
      path.join(root, "lakefile.lean"),
      [
        "import Lake",
        "open Lake DSL",
        "package DemoPkg where",
        'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"',
        'require cslib from git "https://github.com/leanprover/cslib" @ "v4.34.1"',
        'require LSpec from git "https://github.com/argumentcomputer/LSpec" @ "main"',
        'lean_lib DemoPkg where srcDir := "."',
      ].join("\n"),
      "utf-8"
    );
    fs.writeFileSync(
      path.join(root, "lake-manifest.json"),
      JSON.stringify(
        {
          version: "1.2.0",
          name: "DemoPkg",
          packagesDir: ".lake/packages",
          packages: [
            { type: "git", name: "mathlib", url: "https://github.com/leanprover-community/mathlib4.git", rev: "abc", inputRev: "v4.34.1", inherited: false },
            { type: "git", name: "cslib", url: "https://github.com/leanprover/cslib", rev: "def", inputRev: "v4.34.1", inherited: false },
            { type: "git", name: "LSpec", url: "https://github.com/argumentcomputer/LSpec", rev: "123", inputRev: "main", inherited: false },
            { type: "git", name: "batteries", url: "https://github.com/leanprover-community/batteries", rev: "456", inputRev: "main", inherited: true },
          ],
        },
        null,
        2
      ),
      "utf-8"
    );
    fs.mkdirSync(path.join(root, "DemoPkg"), { recursive: true });
    fs.mkdirSync(path.join(root, ".lake", "build", "lib", "lean", "DemoPkg"), { recursive: true });
    fs.writeFileSync(
      path.join(root, "DemoPkg", "Entry.lean"),
      "import Mathlib.Tactic\nimport Cslib.LTS\ndef x : Nat := 1\n",
      "utf-8"
    );
    fs.writeFileSync(
      path.join(root, ".lake", "build", "lib", "lean", "DemoPkg", "Entry.ilean"),
      JSON.stringify({
        module: "DemoPkg.Entry",
        directImports: ["Mathlib.Tactic", "Cslib.LTS"],
        decls: { x: [2, 0, 2, 16] },
        references: {},
      }),
      "utf-8"
    );

    await runLeanTreeShake({
      projectRoot: root,
      entryModules: ["DemoPkg.Entry"],
      outputDir: outDir,
      anonymize: true,
      packageName: "AnonSlice",
    });

    const emittedLakefile = fs.readFileSync(path.join(outDir, "lakefile.lean"), "utf-8");
    assert.ok(emittedLakefile.includes("require mathlib"), "Used mathlib kept in lakefile");
    assert.ok(emittedLakefile.includes("require cslib"), "Used cslib kept in lakefile");
    assert.ok(!emittedLakefile.includes("LSpec"), `Unused LSpec must be pruned from lakefile:\n${emittedLakefile}`);

    const emittedManifest = JSON.parse(fs.readFileSync(path.join(outDir, "lake-manifest.json"), "utf-8"));
    assert.equal(emittedManifest.packages.some((p) => p.name === "mathlib"), true);
    assert.equal(emittedManifest.packages.some((p) => p.name === "cslib"), true);
    assert.equal(emittedManifest.packages.some((p) => p.name === "batteries"), true, "Inherited transitive dep kept");
    assert.equal(emittedManifest.packages.some((p) => p.name === "LSpec"), false, "Unused LSpec pruned from manifest");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
    fs.rmSync(outDir, { recursive: true, force: true });
  }
});
