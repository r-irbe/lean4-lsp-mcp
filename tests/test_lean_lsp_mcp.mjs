// tools/lean_lsp_mcp/tests/test_lean_lsp_mcp.mjs
// Unit and integration test suite for lean-lsp-mcp standalone module
// Scoped Unicode policy (INV-001; typographic-free by default).

import assert from "node:assert";
import * as path from "node:path";
import * as os from "node:os";
import { fileURLToPath } from "node:url";
import {
    Lean4IleanIndex,
    LeanSysrootBridge,
    formatGoalAsMarkdown,
    McpServer,
} from "../src/index.ts";

import * as fs from "node:fs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
const repoRoot = process.env.LEAN_PROJECT_ROOT || pkgRoot;

console.log("=== Testing lean4-lsp-mcp Suite ===");

// 1. formatGoalAsMarkdown
{
    const emptyGoal = formatGoalAsMarkdown("");
    assert.strictEqual(
        emptyGoal,
        "No active goals (proof complete or out of tactic scope).",
        "Empty goal string returns proof complete message"
    );

    const activeGoal = formatGoalAsMarkdown("case intro\nx : Nat\n|- x + 0 = x");
    assert.strictEqual(
        activeGoal,
        "```lean\ncase intro\nx : Nat\n|- x + 0 = x\n```",
        "Active goal formatted with lean markdown block"
    );
    const fencedGoal = formatGoalAsMarkdown("```lean\nx : Nat\n|- x = x\n```");
    assert.strictEqual(
        fencedGoal,
        "```lean\nx : Nat\n|- x = x\n```",
        "Already-fenced plainGoal output is not double-wrapped"
    );
    console.log("  - formatGoalAsMarkdown: PASS");
}

// 2. LeanSysrootBridge
{
    const flags = LeanSysrootBridge.getIncludeFlags();
    assert(Array.isArray(flags), "Flags is an array");
    if (flags.length > 0) {
        assert(flags[0].startsWith("-I"), "First flag starts with -I");
        assert(flags.some(f => f.includes("include")), "Contains include directory");
    }
    const ffiReport = LeanSysrootBridge.inspectFFI(repoRoot, "nonexistent_extern");
    assert(ffiReport.includes("Lean 4 C FFI Environment"), "FFI report contains header");

    const resolveReport = LeanSysrootBridge.inspectFFI(repoRoot, "nonexistent_extern", "resolve_symbol");
    assert(resolveReport.includes("Bidirectional C FFI Resolution"), "FFI resolveReport contains header");
    assert(resolveReport.includes("Lean -> C External Declarations"), "Contains Lean -> C section");
    assert(resolveReport.includes("C -> Lean Function Bindings"), "Contains C -> Lean section");

    const headerReport = LeanSysrootBridge.inspectFFI(repoRoot, undefined, "verify_headers");
    assert(headerReport.includes("C FFI Header & Signature Verification"), "Header verification contains header");

    console.log("  - LeanSysrootBridge (Bidirectional C FFI & Header Verification): PASS");
}

// 3. Lean4IleanIndex
{
    const index = new Lean4IleanIndex(repoRoot);
    const missing = index.lookupSymbol("NonExistentSymbol12345");
    assert.strictEqual(missing, null, "Missing symbol lookup returns null");
    console.log("  - Lean4IleanIndex: PASS");
}

// 4. McpServer Protocol Handlers (In-memory)
{
    const server = new McpServer(repoRoot);

    const initRes = await server.handleMessage({
        jsonrpc: "2.0",
        id: 1,
        method: "initialize",
        params: {
            protocolVersion: "2024-11-05",
            capabilities: {},
            clientInfo: { name: "test-client", version: "1.0.0" },
        },
    });
    assert(initRes && initRes.result.serverInfo.name === "lean-lsp-mcp", "initialize response ok");

    const listRes = await server.handleMessage({
        jsonrpc: "2.0",
        id: 2,
        method: "tools/list",
    });
    assert(listRes && Array.isArray(listRes.result.tools), "tools list is array");
    const toolNames = listRes.result.tools.map(t => t.name);
    assert.strictEqual(toolNames.length, 26, "Exposes 26 canonical tools including autoslim and the three graph engines");

    const expectedTools = [
        "lean_goal", "lean_search", "lean_blueprint", "lean_metrics", "lean_ffi", "lean_exec", "lean_resync",
        "lean_lookup_symbol", "lean_module_hierarchy", "lean_axiom_closure", "lean_navigate", "lean_diagnostics",
        "lean_server_status", "lean_decl_references", "lean_counterexample_search",
        "lean_multi_attempt", "lean_repair_proof", "lean_minimal_hypotheses",
        "lean_profile_proof", "lean_skill_dispatch", "lean_theorem_preflight", "lean_autoslim", "lean_tree_shake",
        "lean_cone_query", "lean_proof_clones", "lean_kernel_whnf_hotspots"
    ];
    for (const t of expectedTools) {
        assert(toolNames.includes(t), `Includes canonical tool: ${t}`);
    }
    const retiredLegacyWrappers = [
        "lean_run_code", "lean_book_index_lookup", "lean_cross_itp_concordance",
        "lean_proof_skeleton", "lean_blueprint_scaffold", "lean_dependency_subgraph", "lean_module_census"
    ];
    for (const legacy of retiredLegacyWrappers) {
        assert(!toolNames.includes(legacy), `Retired legacy wrapper must not appear in tools/list: ${legacy}`);
    }

    // F3-class pin (adopted from the pi-lens #2939 slice-2 pins): the
    // advertised surface and the executeTool switch must not diverge -
    // every advertised name must have a dispatch case, or the tool is
    // discoverable but dead at call time.
    const indexSrc = fs.readFileSync(new URL('../src/index.ts', import.meta.url), 'utf8');
    const caseNames = new Set([...indexSrc.matchAll(/case "([^"]+)"/g)].map(m => m[1]));
    const unbacked = toolNames.filter(n => !caseNames.has(n));
    assert.deepStrictEqual(unbacked, [], 'every advertised tool must have an executeTool case');

    // Protocol behavior when an explicit graph archive cannot be loaded.
    // Browsing a configured graph is covered by the synthetic ZIP in test_mcp_upgrades.
    const previousGraph = server.kuzuGraph;
    const { KuzuKnowledgeGraph } = await import("../src/kuzu_graph.ts");
    const missingGraphDir = fs.mkdtempSync(path.join(os.tmpdir(), "missing-graph-"));
    try {
        server.kuzuGraph = new KuzuKnowledgeGraph(path.join(missingGraphDir, "missing.kz"));
        for (const [name, args] of [
            ["lean_search", { query: "induction", source: "graph" }],
            ["lean_blueprint", { action: "graph_neighborhood", sectionId: "example" }],
        ]) {
            const response = await server.handleMessage({
                jsonrpc: "2.0", id: 3, method: "tools/call",
                params: { name, arguments: args },
            });
            assert(response && response.result && !response.result.isError);
            assert.match(response.result.content[0].text, /configured Kuzu archive could not be loaded/);
        }
    } finally {
        server.kuzuGraph = previousGraph;
        fs.rmSync(missingGraphDir, { recursive: true, force: true });
    }

    // Consolidated lean_search: ontology source
    const callOnto = await server.handleMessage({
        jsonrpc: "2.0",
        id: 5,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "liquid", source: "ontology" },
        },
    });
    assert(callOnto && callOnto.result && callOnto.result.content[0].text.includes("CONCEPT-CONDENSED-MATHEMATICS-LIQUID-VECTOR-SPACES"), "Ontology search resolves concept");

    // Consolidated lean_search: book source
    const callBook = await server.handleMessage({
        jsonrpc: "2.0",
        id: 6,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "category", source: "book" },
        },
    });
    assert(callBook && callBook.result && callBook.result.content[0].text.includes("category"), "Book index lookup resolves entries");

    // Canonical lean_search with book source and prover filter
    const callBookFiltered = await server.handleMessage({
        jsonrpc: "2.0",
        id: 61,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "inversion", source: "book", prover: "lean4" },
        },
    });
    assert(callBookFiltered && callBookFiltered.result && callBookFiltered.result.content[0].text.includes("inversion"), "Filtered book index lookup resolves entries");

    // Consolidated lean_search: concordance source
    const callConc = await server.handleMessage({
        jsonrpc: "2.0",
        id: 7,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "functor", source: "concordance" },
        },
    });
    assert(callConc && callConc.result && callConc.result.content[0].text.length > 0, "Cross-ITP concordance resolves entries");

    // Canonical lean_search concordance source with canonical mechanisms
    const callDirectConc = await server.handleMessage({
        jsonrpc: "2.0",
        id: 71,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "induction", source: "concordance" },
        },
    });
    assert(callDirectConc && callDirectConc.result && callDirectConc.result.content[0].text.includes("CONC-01-CASE-INDUCTION"), "Cross-ITP concordance finds CONC-01");
    assert(callDirectConc.result.content[0].text.includes("rcases"), "Concordance includes Lean 4 rcases");
    assert(callDirectConc.result.content[0].text.includes("coq_mathcomp"), "Concordance includes MathComp");

    // Canonical lean_search concordance with directional translation filter
    const callDirectedConc = await server.handleMessage({
        jsonrpc: "2.0",
        id: 72,
        method: "tools/call",
        params: {
            name: "lean_search",
            arguments: { query: "reflection", source: "concordance", source_prover: "coq_mathcomp", target_prover: "lean4" },
        },
    });
    assert(callDirectedConc && callDirectedConc.result && callDirectedConc.result.content[0].text.includes("CONC-02-BOOLEAN-REFLECTION"), "Directional concordance finds CONC-02");
    assert(callDirectedConc.result.content[0].text.includes("apply/idP"), "Directional concordance includes source pattern apply/idP");
    assert(callDirectedConc.result.content[0].text.includes("decide_eq_true_iff"), "Directional concordance includes target pattern decide_eq_true_iff");

    // Consolidated lean_metrics: census
    const callCensus = await server.handleMessage({
        jsonrpc: "2.0",
        id: 8,
        method: "tools/call",
        params: {
            name: "lean_metrics",
            arguments: { action: "census", target: "src" },
        },
    });
    assert(callCensus && callCensus.result && !callCensus.result.isError, "Module census succeeds");

    // Consolidated lean_metrics: bigraph projection
    const leanRulesPath = path.resolve(__dirname, "../../rust-mmap-engine/lean_rules");
    const testTarget = fs.existsSync(leanRulesPath) ? leanRulesPath : "src";
    const callBigraph = await server.handleMessage({
        jsonrpc: "2.0",
        id: 81,
        method: "tools/call",
        params: {
            name: "lean_metrics",
            arguments: { action: "bigraph", target: testTarget, format: "json" },
        },
    });
    assert(callBigraph && callBigraph.result && !callBigraph.result.isError, "Bigraph projection succeeds");
    const bigraphData = JSON.parse(callBigraph.result.content[0].text);
    assert(bigraphData.place_graph && Array.isArray(bigraphData.place_graph.nodes), "Bigraph contains place_graph nodes");
    assert(bigraphData.link_graph && Array.isArray(bigraphData.link_graph.hyperedges), "Bigraph contains link_graph hyperedges");

    // Consolidated lean_metrics: axiom audit
    const callAxioms = await server.handleMessage({
        jsonrpc: "2.0",
        id: 82,
        method: "tools/call",
        params: {
            name: "lean_metrics",
            arguments: { action: "axiom_audit", target: testTarget, format: "json" },
        },
    });
    assert(callAxioms && callAxioms.result && !callAxioms.result.isError, "Axiom audit succeeds");
    const axiomData = JSON.parse(callAxioms.result.content[0].text);
    assert(axiomData.clean === true, "Axiom audit clean pass verified");
    assert(axiomData.custom_axioms.length === 0, "Zero custom axioms verified");
    assert(axiomData.sorries.length === 0, "Zero sorries verified");

    // Consolidated lean_ffi: sysroot flags
    const callFfi = await server.handleMessage({
        jsonrpc: "2.0",
        id: 9,
        method: "tools/call",
        params: {
            name: "lean_ffi",
            arguments: { action: "sysroot" },
        },
    });
    assert(callFfi && callFfi.result && callFfi.result.content[0].text.includes("Lean Sysroot"), "FFI sysroot query succeeds");

    // Legacy tool routing (backward-compatibility)
    const callLegacy = await server.handleMessage({
        jsonrpc: "2.0",
        id: 10,
        method: "tools/call",
        params: {
            name: "lean_ontology_search",
            arguments: { query: "liquid" },
        },
    });
    assert(callLegacy && callLegacy.result && callLegacy.result.content[0].text.includes("CONCEPT-CONDENSED-MATHEMATICS-LIQUID-VECTOR-SPACES"), "Legacy alias routing works");

    server.dispose();
    console.log("  - McpServer Dispatch (6 consolidated tools + Kuzu graph + legacy aliases): PASS");
}

// 5. LakeBuildGuard Concurrency Check
{
    const { LakeBuildGuard } = await import("../src/index.ts");
    const status = LakeBuildGuard.checkLock(repoRoot);
    assert(typeof status.isLocked === "boolean", "isLocked is a boolean");
    assert(typeof status.source === "string", "source is a string");
    console.log("  - LakeBuildGuard: PASS (isLocked=" + status.isLocked + ", source=" + status.source + ")");
}


// 6. SharedMemorySnapshotRing Lock-Free IPC
{
    const { SharedMemorySnapshotRing } = await import("../src/index.ts");
    const testShmPath = path.join(os.tmpdir(), `test_lean_shm_${process.pid}.shm`);
    const ring = SharedMemorySnapshotRing.create(testShmPath, 8, 4096);
    assert(ring !== null, "SharedMemorySnapshotRing created successfully");

    const seq = ring.writeSnapshot("/repo/Test.lean", 42, 10, "case intro\n|- True", 1, 1);
    assert.strictEqual(seq, 1n, "First write sequence is 1");

    const latest = ring.readLatest();
    assert(latest !== null, "Latest snapshot is readable");
    assert.strictEqual(latest.seq, 1n, "Snapshot sequence matches");
    assert.strictEqual(latest.filePath, "/repo/Test.lean", "Snapshot filePath matches");
    assert.strictEqual(latest.line, 42, "Snapshot line matches");
    assert.strictEqual(latest.col, 10, "Snapshot col matches");
    assert.strictEqual(latest.goalText, "case intro\n|- True", "Snapshot goalText matches");

    ring.dispose();
    console.log("  - SharedMemorySnapshotRing: PASS");
}

// 7. MultiPackageWorkspaceCoordinator & Global Build Lock Arbitration
{
    const { MultiPackageWorkspaceCoordinator, LakeBuildGuard } = await import("../src/index.ts");
    const testWs = fs.mkdtempSync(path.join(os.tmpdir(), "lean_ws_"));
    const pkgADir = path.join(testWs, "packages", "pkg-a");
    const pkgBDir = path.join(testWs, "packages", "pkg-b");
    fs.mkdirSync(pkgADir, { recursive: true });
    fs.mkdirSync(pkgBDir, { recursive: true });
    fs.writeFileSync(path.join(pkgADir, "lakefile.lean"), "-- pkg-a");
    fs.writeFileSync(path.join(pkgBDir, "lakefile.toml"), 'name = "pkg-b"');

    const coord = new MultiPackageWorkspaceCoordinator(testWs);
    const count = coord.getPackageCount();
    assert.strictEqual(count, 2, "Discovered exactly 2 mock Lean packages");

    const resolved = coord.resolvePackageForFile(path.join(pkgADir, "PkgA", "Main.lean"));
    assert(resolved !== null, "Resolved package for pkg-a file");
    assert.strictEqual(resolved.name, "pkg-a", "Package name matches pkg-a");

    // Test global build lock detection. NOTE: this path is REAL and
    // shared with live tooling (the concurrent session's builds use the
    // same file). Save any existing lock, write ours, and restore theirs
    // only when our own write is still in place - a concurrent writer
    // always wins the file, never our restore. If a concurrent writer
    // replaced the lock between our write and the check, the guard still
    // detected an active build; assert the tolerant contract then.
    const testGlobalLock = "/dev/shm/lean_global_workspace.lock";
    let priorLock = null;
    try { priorLock = fs.readFileSync(testGlobalLock, "utf-8"); } catch {}
    const lockInfo = {
        pid: process.pid,
        packageName: "pkg-a",
        acquiredAt: Date.now(),
        ttlMs: 60000,
    };
    fs.writeFileSync(testGlobalLock, JSON.stringify(lockInfo));

    const status = LakeBuildGuard.checkLock(testWs);
    assert.strictEqual(status.isLocked, true, "Global workspace lock detected");
    let oursStill = true;
    try {
        oursStill = JSON.parse(fs.readFileSync(testGlobalLock, "utf-8")).pid === process.pid;
    } catch { oursStill = false; }
    if (oursStill) {
        assert.strictEqual(status.source, "global_workspace_lock", "Source is global_workspace_lock");
        assert(status.detail && status.detail.includes("pkg-a"), "Detail mentions active package");
    } else {
        // a concurrent writer won the shared path mid-test; the guard's
        // detection still fired on a live source
        assert(["global_workspace_lock", "process_table"].includes(status.source),
            "Concurrent lock race: an active build is still detected");
    }

    if (oursStill) {
        try {
            if (priorLock !== null) fs.writeFileSync(testGlobalLock, priorLock);
            else fs.unlinkSync(testGlobalLock);
        } catch {}
    }
    fs.rmSync(testWs, { recursive: true, force: true });
    console.log("  - MultiPackageWorkspaceCoordinator: PASS (packages=" + count + ")");
}

// 8. BitsetDAGIndex topological longest-path depth & cycle detection (BUG-1)
{
    const { BitsetDAGIndex } = await import("../src/index.ts");
    const dag = new BitsetDAGIndex();
    // Diamond DAG: A -> B -> C -> D and A -> D (longest path = 3, shortest BFS path = 2)
    dag.build(new Map([
        ["A", ["B", "D"]],
        ["B", ["C"]],
        ["C", ["D"]],
        ["D", []],
    ]));

    const unprecomputed = dag.getTransitiveClosure("A", "imports", 20);
    assert.strictEqual(unprecomputed.depth, 3, "Topological longest-path depth on diamond DAG is 3 without precompute");
    assert.strictEqual(unprecomputed.hasCycle, false, "Diamond DAG has no cycle");
    assert.strictEqual(unprecomputed.items.length, 3, "Reachable items count is 3");

    const precomputedOk = dag.precomputeClosureMatrix();
    assert.strictEqual(precomputedOk, true, "precomputeClosureMatrix succeeds on acyclic DAG");
    const precomputed = dag.getTransitiveClosure("A", "imports", 20);
    assert.strictEqual(precomputed.depth, 3, "Topological longest-path depth on diamond DAG is 3 with precomputed matrix");
    assert.strictEqual(precomputed.hasCycle, false, "Diamond DAG has no cycle with precomputed matrix");

    // Cyclic graph: X -> Y -> Z -> Y
    const cyclic = new BitsetDAGIndex();
    cyclic.build(new Map([
        ["X", ["Y"]],
        ["Y", ["Z"]],
        ["Z", ["Y"]],
    ]));
    assert.strictEqual(cyclic.precomputeClosureMatrix(), false, "precomputeClosureMatrix detects cycle");
    const cycRes = cyclic.getTransitiveClosure("X", "imports", 20);
    assert.strictEqual(cycRes.hasCycle, true, "getTransitiveClosure reports hasCycle=true on cyclic graph");
    assert(Array.isArray(cycRes.cyclePath) && cycRes.cyclePath.length >= 2, "cyclePath populated");
    console.log("  - BitsetDAGIndex (topological longest-path depth & cycle detection): PASS");
}

// 9. KuzuKnowledgeGraph parameterized / env-configured paths (BUG-2/7/8)
{
    const { KuzuKnowledgeGraph } = await import("../src/kuzu_graph.ts");
    const customDbDir = path.join(os.tmpdir(), `test_kuzu_db_${process.pid}`);
    const prevEnv = process.env.KUZU_DB_PATH;
    process.env.KUZU_DB_PATH = customDbDir;
    try {
        const kgEnv = new KuzuKnowledgeGraph();
        assert.strictEqual(kgEnv.dbPath, customDbDir, "KUZU_DB_PATH env configures dbPath");
    } finally {
        if (prevEnv === undefined) delete process.env.KUZU_DB_PATH;
        else process.env.KUZU_DB_PATH = prevEnv;
    }
    const kgOpt = new KuzuKnowledgeGraph({ dbPath: "/tmp/custom-opt-kuzu" });
    assert.strictEqual(kgOpt.dbPath, "/tmp/custom-opt-kuzu", "options.dbPath configures dbPath");
    console.log("  - KuzuKnowledgeGraph (parameterized & env-configured dbPath): PASS");
}

// 10. AltProof Hybrid Integration (LeanAbstractInterpreter + McpServer lean_goal/lean_metrics/lean_altproof)
{
    const { McpServer, LeanAbstractInterpreter, ALTPROOF_ROUTE_TABLE } = await import("../src/index.ts");
    assert.strictEqual(ALTPROOF_ROUTE_TABLE.length, 20, "ALTPROOF_ROUTE_TABLE exposes all 20 canonical routes");
    const interp = new LeanAbstractInterpreter();

    // 10a. Pointwise sum monotonicity (finset_mono) + static Nat certificate
    const monoReport = interp.analyzeAltProof(
        "Finset.sum s (fun i => c i * f i) <= Finset.sum s (fun i => c i * g i)",
        "  have h := Nat.div 10 0\n  refine Finset.sum_le_sum fun i _ => ?_\n  exact mul_le_mul_of_nonneg_left (hfg i) (hc i)"
    );
    assert.strictEqual(monoReport.features.hasFinsetSum, true, "Detects Finset.sum feature");
    assert.strictEqual(monoReport.features.hasFinsetMono, true, "Detects Finset.sum monotonicity feature");
    assert.strictEqual(monoReport.bestTactic, "finset_mono", "Ranks finset_mono first for sum <= sum goal");
    assert.strictEqual(monoReport.legibility.steps, 3, "Counts 3 non-comment proof steps");
    assert.strictEqual(monoReport.legibility.verboseScore, 1.0, "All 3 steps are renderable");
    assert.strictEqual(monoReport.staticCertificates.length, 1, "LeanAbstractInterpreter detects Nat.div 10 0 hazard");
    assert.strictEqual(monoReport.staticCertificates[0].kind, "NatDivModByZero", "Certificate kind is NatDivModByZero");

    // 10b. McpServer dispatch via lean_altproof, lean_goal (target: "altproof"), and lean_metrics (action: "altproof")
    const server = new McpServer(process.cwd());
    try {
        const mdOut = await server.executeTool("lean_altproof", {
            goal: "0 <= Finset.sum s (fun i => d i * (u i) ^ 2)",
            proof: "  finset_nonneg"
        });
        assert(mdOut.includes("AltProof Hybrid Tactic & Route Advisor"), "Markdown header rendered");
        assert(mdOut.includes("`finset_nonneg`"), "Recommends finset_nonneg");

        const jsonViaGoal = await server.executeTool("lean_goal", {
            target: "altproof",
            goal: "Opinion.WellFormed op",
            proof: "  wellformed_tac [op]",
            format: "json"
        });
        const parsedGoal = JSON.parse(jsonViaGoal);
        assert.strictEqual(parsedGoal.bestTactic, "wellformed_tac", "lean_goal target=altproof recommends wellformed_tac");

        const jsonViaMetrics = await server.executeTool("lean_metrics", {
            action: "altproof",
            target: "Channel (Fin 3) (Fin 2)",
            format: "json"
        });
        const parsedMetrics = JSON.parse(jsonViaMetrics);
        assert.strictEqual(parsedMetrics.bestTactic, "channel_fields", "lean_metrics action=altproof recommends channel_fields");

        // Check the executable AltProof routes against the same proof shapes as the CLI.
        const parityCases = [
            ["\u22a2 (17 : Nat) % 3 = 2", "by decide +kernel", ["sair_decide"]],
            ["a b c : Alpha\nhab : a = b\nhbc : b = c\n\u22a2 f a = f c", "by rw [hab, hbc]", ["eqsat_rw"]],
            ["p q r : Prop\nhp : p\nhpq : p \u2192 q\nhqr : q \u2192 r\n\u22a2 r", "by apply hqr; apply hpq; exact hp", ["backchain", "solve_by_elim"]],
            ["x : Nat\n\u22a2 x = x", "by rfl", []],
        ];
        for (const [goal, proof, expected] of parityCases) {
            const report = JSON.parse(await server.executeTool("lean_goal", {
                target: "altproof", goal, proof, format: "json",
            }));
            assert.deepEqual(report.recommendations.map(({ tactic }) => tactic), expected, proof);
        }

        // 10c. Multiline LSP goal turnstile isolation (hypotheses before |- do not bleed into target conclusion)
        const multilineGoal = [
            "s : Finset Nat",
            "f : Nat -> Real",
            "h_le : Finset.sum s f <= 1",
            "h_nonneg : 0 <= c",
            "|- Finset.sum s (fun i => 2 * f i) = Finset.sum s (fun i => f i + f i)"
        ].join("\n");
        const multiReport = interp.analyzeAltProof(multilineGoal, "");
        assert.strictEqual(multiReport.features.hasFinsetMono, false, "Hypothesis <= does not trigger hasFinsetMono on equality target");
        assert.strictEqual(multiReport.features.hasFinsetNonneg, false, "Hypothesis 0 <= does not trigger hasFinsetNonneg on equality target");
        assert.strictEqual(multiReport.bestTactic, "sum_congr_ring", "Multiline LSP sum equality selects sum_congr_ring");

        // 10d. Symbolic Finset.sum over Fin n does not recommend decide ahead of sum_congr_ring
        const finSumReport = interp.analyzeAltProof(
            "Finset.sum univ (fun i : Fin 3 => 2 * f i) = Finset.sum univ (fun i : Fin 3 => f i + f i)",
            ""
        );
        assert.strictEqual(finSumReport.bestTactic, "sum_congr_ring", "Symbolic Finset.sum over Fin 3 selects sum_congr_ring, not decide");
        assert(!finSumReport.recommendations.some(r => r.tactic === "decide"), "decide suppressed on Finset.sum goal");

        // 10e. Live LSP session goal extraction path via lakeManager.getGoal when (filePath, line, col) is passed without explicit goal
        const lm = server.getLakeManager();
        lm.sessions.set(server.leanRoot, { lastUsed: Date.now() });
        lm.getGoal = async (_filePath, line, col) => {
            return `\`\`\`lean\nh : 0 <= w i\n|- Finset.sum s (fun i => w i * f i) <= Finset.sum s (fun i => w i * g i)\n\`\`\` (at ${line}:${col})`;
        };
        const liveSessionJson = await server.executeTool("lean_altproof", {
            filePath: "MyProject/Tests/TacticAltProof.lean",
            line: 40,
            col: 4,
            proof: "  finset_mono",
            format: "json"
        });
        const parsedLive = JSON.parse(liveSessionJson);
        assert.strictEqual(parsedLive.bestTactic, "finset_mono", "Live LSP goal fetched via lakeManager.getGoal and dispatched to finset_mono");
        assert.strictEqual(parsedLive.features.hasFinsetNonneg, false, "Turnstile isolation holds on fenced LSP getGoal output");

        // 10f. AltProof v0.5.0+ double-sum calc_ring_sum, Kronecker-delta Finset.sum_ite_eq, eqsat_rw, contra_direct, and Lean 4.34 hygiene
        const dblSumReport = interp.analyzeAltProof(
            "|- Finset.sum s (fun i => Finset.sum t (fun j => f i * g j)) = (Finset.sum s f) * (Finset.sum t g)",
            "  rw [Finset.sum_comm]"
        );
        assert.strictEqual(dblSumReport.bestTactic, "calc_ring_sum", "Double-sum commutation selects calc_ring_sum ahead of sum_congr_ring");

        const kroneckerReport = interp.analyzeAltProof(
            "|- Finset.sum s (fun i => if i = j then f i else 0) = f j",
            "  rw [Finset.sum_eq_single j]\n  if h : j = j then simp else simp"
        );
        assert(kroneckerReport.bestTactic && kroneckerReport.bestTactic.includes("Finset.sum_ite_eq"), "Kronecker-delta sum selects Finset.sum_ite_eq collapse");

        const eqsatReport = interp.analyzeAltProof(
            "a b : Alpha |- f (g a) = f b",
            "  push_neg\n  eqsat_rw [h1, h2]"
        );
        assert(eqsatReport.recommendations.some((r) => r.tactic === "eqsat_rw"), "Recommends eqsat_rw on pure congruence goal");
        assert(eqsatReport.staticCertificates.some((c) => c.operator === "push_neg"), "Flags deprecated push_neg under Lean 4.34");

        const contraReport = interp.analyzeAltProof(
            "P Q : Prop |- Not P -> P -> Q",
            "  by_contra h"
        );
        assert.strictEqual(contraReport.bestTactic, "contra_direct", "Contradiction redirect selects contra_direct");
    } finally {
        server.getLakeManager().dispose();
    }
    console.log("  - AltProof Hybrid Integration (LeanAbstractInterpreter + McpServer): PASS");
}

// 11. bin/lean-lsp-mcp.js stdio entrypoint starts main() even when dist/index.js is fresh
{
    const { spawn: spawnChild } = await import("node:child_process");
    const binPath = path.resolve(import.meta.dirname, "../bin/lean-lsp-mcp.js");
    const distIndex = path.resolve(import.meta.dirname, "../dist/index.js");
    const srcIndex = path.resolve(import.meta.dirname, "../src/index.ts");
    if (fs.existsSync(distIndex) && fs.existsSync(srcIndex)) {
        const future = new Date(Date.now() + 2000);
        fs.utimesSync(distIndex, future, future);
    }
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "bin-entry-"));
    try {
        const child = spawnChild(process.execPath, [binPath], {
            cwd: tmp,
            env: { ...process.env, LEAN_SHM_PATH: path.join(tmp, "bin.shm"), NODE_NO_WARNINGS: "1" },
            stdio: ["pipe", "pipe", "pipe"]
        });
        const reply = await new Promise((resolve, reject) => {
            const t = setTimeout(() => reject(new Error("bin/lean-lsp-mcp.js timed out on initialize")), 5000);
            let outBuf = "";
            child.stdout.setEncoding("utf-8");
            child.stdout.on("data", (chunk) => {
                outBuf += chunk;
                const nl = outBuf.indexOf("\n");
                if (nl !== -1) {
                    clearTimeout(t);
                    resolve(JSON.parse(outBuf.slice(0, nl)));
                }
            });
            child.on("exit", (code) => {
                clearTimeout(t);
                reject(new Error(`bin/lean-lsp-mcp.js exited early with code ${code}`));
            });
            child.stdin.write(JSON.stringify({ jsonrpc: "2.0", id: 1, method: "initialize", params: {} }) + "\n");
        });
        assert.strictEqual(reply.result.serverInfo.version, "0.7.0", "bin/lean-lsp-mcp.js starts stdio server via dist/index.js");
        child.stdin.end();
        child.kill("SIGTERM");
        console.log("  - bin/lean-lsp-mcp.js stdio entrypoint (fresh dist/index.js): PASS");
    } finally {
        fs.rmSync(tmp, { recursive: true, force: true });
    }
}

// 12. The launcher prefers compiled code under node_modules and editable source elsewhere.
{
    const { spawnSync } = await import("node:child_process");
    const bin = path.resolve(import.meta.dirname, "../bin/lean-lsp-mcp.js");
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "mcp-launch-layout-"));
    try {
        for (const [layout, installed, hoisted, withDist, withDependencies, expected] of [
            ["hoisted", true, true, true, true, "dist"],
            ["nested", true, false, true, true, "dist"],
            ["editable", false, false, true, true, "source"],
            ["missing-dist", true, false, false, true, /missing dist\/index\.js/],
            ["installed-missing-deps", true, false, true, false, /Missing runtime dependencies\. Reinstall lean4-lsp-mcp\./],
            ["missing-deps", false, false, true, false, /Failed to bootstrap node_modules/],
        ]) {
            const consumer = path.join(tmp, layout);
            const pkg = installed ? path.join(consumer, "node_modules/lean4-lsp-mcp") : consumer;
            for (const dir of ["bin", "src", "dist"]) fs.mkdirSync(path.join(pkg, dir), { recursive: true });
            const launcher = path.join(pkg, "bin/lean-lsp-mcp.js");
            fs.copyFileSync(bin, launcher);
            fs.writeFileSync(path.join(pkg, "package.json"), '{"type":"module"}');
            fs.writeFileSync(path.join(pkg, "src/index.ts"), 'const entry: string = "source"; console.log(entry);');
            if (withDist) {
                const dist = path.join(pkg, "dist/index.js");
                fs.writeFileSync(dist, 'export function main() { console.log("dist"); }');
                fs.utimesSync(dist, new Date(0), new Date(0));
            }
            if (withDependencies) {
                const deps = path.join(hoisted ? consumer : pkg, "node_modules");
                for (const name of ["@modelcontextprotocol/sdk", "js-yaml"]) {
                    const dep = path.join(deps, name);
                    fs.mkdirSync(dep, { recursive: true });
                    fs.writeFileSync(path.join(dep, "package.json"), '{"main":"index.js"}');
                    fs.writeFileSync(path.join(dep, "index.js"), "");
                }
            }
            const result = spawnSync(process.execPath, [launcher], {
                cwd: consumer, env: { ...process.env, PATH: "" }, encoding: "utf8", timeout: 5000,
            });
            assert.ifError(result.error);
            if (expected instanceof RegExp) {
                assert.equal(result.status, 1, `${layout}: ${result.stderr}`);
                assert.match(result.stderr, expected, layout);
                assert.equal(result.stdout, "", layout);
                if (installed) assert.doesNotMatch(result.stderr, /Bootstrapping/, layout);
            } else {
                assert.equal(result.status, 0, `${layout}: ${result.stderr}`);
                assert.equal(result.stdout.trim(), expected, layout);
                assert.equal(result.stderr, "", layout);
            }
        }
        console.log("  - bin/lean-lsp-mcp.js installed and editable layouts: PASS");
    } finally {
        fs.rmSync(tmp, { recursive: true, force: true });
    }
}

console.log("=== All lean4-lsp-mcp Tests Passed ===");


