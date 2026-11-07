// P1 operations: each operation reaches the expected LSP method with the right arguments.
import assert from "node:assert/strict";
import { test, mock } from "node:test";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import cp from "node:child_process";
import { syncBuiltinESMExports } from "node:module";
import { McpServer } from "../src/index.ts";
import { buildNavRequest, boundNavResult, NAV_MAX_ITEMS, NavRefusal } from "../src/navigation.ts";
import { makeFakeLsp } from "./nav_fake_lsp.mjs";

const base = fs.mkdtempSync(path.join(os.tmpdir(), "nav-ops-"));
const prevShm = process.env.LEAN_SHM_PATH;
process.env.LEAN_SHM_PATH = path.join(base, "snap.shm");
process.env.LEAN_SERVE_DIRECT = "1";

const log = {};
const behavior = {};
mock.method(cp, "execFileSync", () => "Lean (version 4.35.0, fixture)");
mock.method(cp, "execSync", () => "");
mock.method(cp, "spawn", makeFakeLsp(log, behavior));
syncBuiltinESMExports();

const root = path.join(base, "proj");
fs.mkdirSync(root, { recursive: true });
fs.writeFileSync(path.join(root, "A.lean"), "def a := 1\ntheorem t : a = 1 := rfl\n");
fs.writeFileSync(path.join(root, "B.lean"), "import A\n");
const mods = path.join(base, "mods");
fs.mkdirSync(mods, { recursive: true });
fs.mkdirSync(path.join(base, "bin"), { recursive: true });
const lean = path.join(base, "bin", "lean");
fs.writeFileSync(lean, "fixture", { mode: 0o755 });
const ctx = { compilerPath: lean, targetVersion: "4.35.0", moduleRoots: [mods] };
fs.writeFileSync(path.join(mods, "A.ilean"), JSON.stringify({ module: "A", decls: {}, directImports: [] }));
fs.writeFileSync(path.join(mods, "B.ilean"), JSON.stringify({ module: "B", decls: {}, directImports: [["A"]] }));
const s = new McpServer(root, ctx);
const nav = async (args) => JSON.parse(await s.getLakeManager().navigate(args, s.getIleanIndex()));
const lastRequest = () => log.requests[log.requests.length - 1];
const uri = pathToFileURL(path.join(root, "A.lean")).href;

try {
  await test("buildNavRequest maps every LSP-backed operation to its method (pure)", () => {
    const at = { line: 3, col: 5 };
    const expect = {
      hover: "textDocument/hover", definition: "textDocument/definition", typeDefinition: "textDocument/typeDefinition",
      declaration: "textDocument/declaration", implementation: "textDocument/implementation",
      references: "textDocument/references", documentSymbol: "textDocument/documentSymbol",
      workspaceSymbol: "workspace/symbol", findSymbol: "workspace/symbol",
      prepareCallHierarchy: "textDocument/prepareCallHierarchy", codeAction: "textDocument/codeAction",
    };
    for (const [operation, method] of Object.entries(expect)) {
      const r = buildNavRequest({ operation, query: "q", ...at }, "file:///x.lean");
      assert.equal(r.method, method, operation);
    }
    const r = buildNavRequest({ operation: "hover", ...at }, "file:///x.lean");
    assert.deepEqual(r.params.position, { line: 2, character: 4 }, "1-based -> 0-based");
    const item = { uri: "file:///x.lean", name: "f" };
    assert.equal(buildNavRequest({ operation: "incomingCalls", callHierarchyItem: item }).method, "callHierarchy/incomingCalls");
    assert.equal(buildNavRequest({ operation: "outgoingCalls", callHierarchyItem: item }).method, "callHierarchy/outgoingCalls");
    assert.equal(buildNavRequest({ operation: "references", ...at, includeDeclaration: false }, "u").params.context.includeDeclaration, false);
  });

  await test("document operations sync the document and send the mapped request through the live session", async () => {
    for (const operation of ["hover", "definition", "typeDefinition", "declaration", "implementation", "references", "prepareCallHierarchy", "codeAction"]) {
      const out = await nav({ operation, filePath: "A.lean", line: 2, col: 9 });
      assert.equal(out.route, "live", operation);
      assert.equal(out.mode, "exact");
      const req = lastRequest();
      assert.equal(req.params.textDocument.uri, uri, operation);
      assert.deepEqual(req.params.position ?? req.params.range.start, { line: 1, character: 8 }, operation);
    }
    await nav({ operation: "documentSymbol", filePath: "A.lean" });
    assert.equal(lastRequest().method, "textDocument/documentSymbol");
  });

  await test("codeAction is advertise-only: edit/command payloads never leave the server", async () => {
    behavior["textDocument/codeAction"] = () => [{ title: "Fix", kind: "quickfix", edit: { changes: {} }, command: { command: "x" }, isPreferred: true }];
    try {
      const out = await nav({ operation: "codeAction", filePath: "A.lean", line: 1, col: 1 });
      assert.deepEqual(out.result, [{ title: "Fix", kind: "quickfix", isPreferred: true }]);
    } finally { delete behavior["textDocument/codeAction"]; }
  });

  await test("findSymbol narrows workspace/symbol to the exact name; workspaceSymbol does not", async () => {
    behavior["workspace/symbol"] = () => [{ name: "Foo.bar" }, { name: "bar" }, { name: "barn" }];
    try {
      const found = await nav({ operation: "findSymbol", filePath: "A.lean", query: "bar" });
      assert.deepEqual(found.result.map((x) => x.name), ["Foo.bar", "bar"]);
      const all = await nav({ operation: "workspaceSymbol", filePath: "A.lean", query: "bar" });
      assert.equal(all.result.length, 3);
    } finally { delete behavior["workspace/symbol"]; }
  });

  await test("call-hierarchy items outside the project and admitted roots are refused before any request", async () => {
    const before = log.requests.length;
    const outside = { uri: pathToFileURL("/etc/passwd").href, name: "x" };
    await assert.rejects(nav({ operation: "incomingCalls", callHierarchyItem: outside }), /admission-missing: incomingCalls: callHierarchyItem\.uri is outside/);
    assert.equal(log.requests.length, before);
    const inside = { uri, name: "a" };
    const out = await nav({ operation: "outgoingCalls", callHierarchyItem: inside });
    assert.equal(lastRequest().method, "callHierarchy/outgoingCalls");
    assert.equal(out.route, "live");
  });

  await test("oversize results are bounded: arrays truncated with a marker, giant payloads refused", () => {
    const big = Array.from({ length: NAV_MAX_ITEMS + 5 }, (_, i) => ({ i }));
    const bounded = boundNavResult("references", big);
    assert.equal(bounded.truncated, true);
    assert.equal(bounded.total, NAV_MAX_ITEMS + 5);
    assert.equal(bounded.items.length, NAV_MAX_ITEMS);
    assert.throws(() => boundNavResult("hover", "x".repeat(300 * 1024)), (e) => e instanceof NavRefusal && e.code === "bounds-exceeded");
  });

  await test("offline fallback only where declared: definition/references with a symbol; else the LSP error surfaces", async () => {
    behavior["textDocument/definition"] = () => ({ __error: "server boom" });
    behavior["textDocument/hover"] = () => ({ __error: "server boom" });
    try {
      await assert.rejects(nav({ operation: "hover", filePath: "A.lean" }), /lean_navigate hover failed: server boom/);
      // definition with no symbol: no fallback
      await assert.rejects(nav({ operation: "definition", filePath: "A.lean" }), /lean_navigate definition failed/);
      // definition with a symbol that the (empty) index cannot resolve: still no silent success
      await assert.rejects(nav({ operation: "definition", filePath: "A.lean", symbol: "nope" }), /lean_navigate definition failed/);
    } finally { delete behavior["textDocument/definition"]; delete behavior["textDocument/hover"]; }
  });

  await test("moduleImports / moduleImportedBy are offline; an unknown module is refused, never an empty success", async () => {
    const imports = await nav({ operation: "moduleImports", filePath: "B.lean" });
    assert.equal(imports.route, "offline");
    assert.equal(imports.result.module, "B");
    assert.deepEqual(imports.result.modules, ["A"]);
    const by = await nav({ operation: "moduleImportedBy", filePath: "A.lean" });
    assert.deepEqual(by.result.modules, ["B"]);
    fs.writeFileSync(path.join(root, "C.lean"), "def c := 0\n"); // exists, but no .ilean in the admitted roots
    await assert.rejects(nav({ operation: "moduleImports", filePath: "C.lean" }), /artifact-unavailable: moduleImports: module C has no \.ilean record/);
  });

  await test("cold-open readiness: unfinished document returning null/[] raises analysis_incomplete, while finished [] returns empty:true", async () => {
    fs.writeFileSync(path.join(root, "D.lean"), "def d := 42\n");
    const prevReady = process.env.LEAN_NAV_READY_MS;
    process.env.LEAN_NAV_READY_MS = "40";
    behavior.__neverFinish = true;
    behavior["textDocument/hover"] = () => null;
    try {
      await assert.rejects(
        nav({ operation: "hover", filePath: "D.lean", line: 1, col: 5 }),
        /analysis_incomplete: hover at D\.lean:1:5/,
      );
    } finally {
      delete behavior.__neverFinish;
      delete behavior["textDocument/hover"];
      if (prevReady === undefined) delete process.env.LEAN_NAV_READY_MS;
      else process.env.LEAN_NAV_READY_MS = prevReady;
    }
    // Now rewrite D.lean so syncDocument bumps version and emits processing:[]; empty codeAction is legitimately empty:true
    fs.writeFileSync(path.join(root, "D.lean"), "def d := 43\n");
    behavior["textDocument/codeAction"] = () => [];
    try {
      const out = await nav({ operation: "codeAction", filePath: "D.lean", line: 1, col: 5 });
      assert.equal(out.empty, true);
      assert.deepEqual(out.result, []);
    } finally {
      delete behavior["textDocument/codeAction"];
    }
  });
} finally {
  s.dispose();
  mock.restoreAll(); syncBuiltinESMExports();
  if (prevShm === undefined) delete process.env.LEAN_SHM_PATH; else process.env.LEAN_SHM_PATH = prevShm;
  fs.rmSync(base, { recursive: true, force: true });
}
