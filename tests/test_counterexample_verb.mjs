// tests/test_counterexample_verb.mjs
// Integration tests for lean_counterexample_search
// (PLAN-LEAN-LSP-MCP-COUNTEREXAMPLE-VERB).
// Auto-skips unless a Lean project with Plausible is reachable.
// Strict 7-bit ASCII only (INV-001).

import assert from "node:assert";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { execSync } from "node:child_process";
import { McpServer } from "../src/index.ts";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const pkgRoot = path.resolve(__dirname, "..");
// ../.. = skills/tools, ../.. = skills, ../.. = the EASCI Lean project.
const corpusRoot =
    process.env.LEAN_PROJECT_ROOT || path.resolve(pkgRoot, "..", "..", "..");

function canRun() {
    try {
        const marker = path.join(
            corpusRoot,
            ".lake",
            "packages",
            "plausible",
            "Plausible.lean"
        );
        if (!fs.existsSync(marker)) return false;
        execSync("lake --version", { stdio: "pipe", timeout: 30000 });
        return true;
    } catch {
        return false;
    }
}

if (!canRun()) {
    console.log(
        "SKIP test_counterexample_verb: lake or Plausible not available at",
        corpusRoot
    );
    process.exit(0);
}

console.log("=== counterexample verb integration suite ===");

const server = new McpServer(corpusRoot);
const fixtures = fs.mkdtempSync(path.join(os.tmpdir(), "ces-fixtures-"));
const fixturePath = path.join(fixtures, "Fixture.lean");
fs.writeFileSync(
    fixturePath,
    [
        "theorem false_stmt : forall n : Nat, n < n := by sorry",
        "",
        "theorem true_stmt : forall n : Nat, n <= n + 100 := by sorry",
        "",
        "theorem unsupported_stmt (p : Nat -> Prop) : p 0 := by sorry",
        "",
        "theorem far_stmt (n : Nat) : n < 150 := by sorry",
        "",
    ].join("\n")
);
const fixtureBytes = fs.readFileSync(fixturePath);

async function call(toolArgs) {
    const res = await server.handleMessage({
        jsonrpc: "2.0",
        id: Math.floor(Math.random() * 1000000),
        method: "tools/call",
        params: { name: "lean_counterexample_search", arguments: toolArgs },
    });
    assert(res && res.result && Array.isArray(res.result.content), "structured tool result");
    return res.result.content.map((c) => c.text).join("\n");
}

// 1. A false statement returns a counterexample with concrete values.
{
    const out = await call({
        filePath: fixturePath,
        theoremName: "false_stmt",
        budgetMs: 60000,
    });
    assert(
        out.startsWith("counterexample"),
        `false statement returns counterexample, got: ${out.slice(0, 90)}`
    );
    assert(/n := \d+/.test(out), "counterexample carries concrete values");
    console.log("  - counterexample path: PASS");
}

// 2. A true statement survives the sample cap.
{
    const out = await call({
        filePath: fixturePath,
        theoremName: "true_stmt",
        samples: 50,
        budgetMs: 60000,
    });
    assert(
        out.startsWith("survived"),
        `true statement survives, got: ${out.slice(0, 90)}`
    );
    assert(out.includes("Evidence, not a proof"), "survived is honest about evidence");
    console.log("  - survived path: PASS");
}

// 3. No testable instance -> unsupported with the reason, not an exception.
{
    const out = await call({
        filePath: fixturePath,
        theoremName: "unsupported_stmt",
        budgetMs: 60000,
    });
    assert(
        out.startsWith("unsupported"),
        `abstract predicate is unsupported, got: ${out.slice(0, 90)}`
    );
    assert(out.includes("testable instance"), "unsupported carries the reason");
    console.log("  - unsupported path: PASS");
}

// 4. budgetMs=1 returns budget_expired deterministically.
{
    const out = await call({
        filePath: fixturePath,
        theoremName: "true_stmt",
        samples: 5,
        budgetMs: 1,
    });
    assert(
        out.startsWith("budget_expired"),
        `budgetMs=1 expires, got: ${out.slice(0, 90)}`
    );
    console.log("  - budget_expired path: PASS");
}

// 5. Invalid import names are rejected (no injection path into the scratch).
{
    const out = await call({
        filePath: fixturePath,
        theoremName: "true_stmt",
        imports: ["Bad Module!"],
        budgetMs: 60000,
    });
    assert(
        out.startsWith("unsupported") && out.includes("invalid import"),
        `invalid import rejected, got: ${out.slice(0, 90)}`
    );
    console.log("  - imports validation: PASS");
}

// 6. Scratch isolation: fixture unchanged, no scratch dirs left behind.
{
    assert(
        Buffer.compare(fixtureBytes, fs.readFileSync(fixturePath)) === 0,
        "fixture file unchanged"
    );
    const leftovers = fs
        .readdirSync(os.tmpdir())
        .filter((name) => name.startsWith("lean-ces-"));
    assert.deepStrictEqual(leftovers, [], "no scratch dirs left behind");
    console.log("  - scratch isolation: PASS");
}

// 7. Single-flight sharing: identical concurrent calls share one execution.
{
    const args = {
        filePath: fixturePath,
        theoremName: "true_stmt",
        samples: 30,
        budgetMs: 60000,
    };
    const first = call(args);
    let registered = false;
    for (let i = 0; i < 300 && !registered; i++) {
        registered = server.counterexampleFlight.inFlightCount() === 1;
        if (!registered) await new Promise((r) => setTimeout(r, 10));
    }
    const second = call(args);
    const [out1, out2] = await Promise.all([first, second]);
    assert(out1 === out2, "shared flight returns the same result to both callers");
    assert.strictEqual(
        server.counterexampleFlight.inFlightCount(),
        0,
        "flight cleared after settle"
    );
    console.log(`  - single-flight sharing: PASS (registered=${registered})`);
}

// 8. Dense strategy: the n < 150 case study - the default shape's
//    sampling misses values >= 150, the wide-size candidate reaches them.
//    (Case pinned empirically: plain survived at 100 instances; maxSize
//    500 refuted with n := 168.)
{
    const sliceOut = await call({
        filePath: fixturePath,
        theoremName: "far_stmt",
        budgetMs: 120000,
    });
    assert(
        sliceOut.startsWith("survived"),
        `slice misses the far counterexample (as pinned), got: ${sliceOut.slice(0, 90)}`
    );
    const denseOut = await call({
        filePath: fixturePath,
        theoremName: "far_stmt",
        strategy: "dense",
        budgetMs: 120000,
        probeBudgetMs: 30000,
    });
    assert(
        denseOut.startsWith("counterexample"),
        `dense finds it, got: ${denseOut.slice(0, 90)}`
    );
    assert(
        denseOut.includes("sized-wide"),
        `dense reports the winning candidate, got: ${denseOut.slice(0, 160)}`
    );
    console.log("  - dense strategy: PASS (v1-unproductive case refuted)");
}

// 9. Unknown strategy values are rejected, not silently coerced.
{
    const out = await call({
        filePath: fixturePath,
        theoremName: "true_stmt",
        strategy: "Bogus",
        budgetMs: 60000,
    });
    assert(
        out.startsWith("unsupported") && out.includes("unknown strategy"),
        `unknown strategy rejected, got: ${out.slice(0, 90)}`
    );
    console.log("  - strategy validation: PASS");
}

try {
    fs.rmSync(fixtures, { recursive: true, force: true });
} catch {
    // best-effort cleanup
}

console.log("counterexample verb suite: ALL PASS");
