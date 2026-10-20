# lean-lsp-mcp: Standalone Lean 4 & C FFI Model Context Protocol Server

`lean-lsp-mcp` is an open-source, standalone Model Context Protocol (MCP) server
providing AI coding agents (Claude Code, Cursor, Windsurf, Zed, Antigravity) with
high-performance tools for Lean 4 formal verification, offline navigation, and C FFI
inspection.

NB! Still pre-alpha!

---

## Install

From npm (published bin `lean-lsp-mcp` / `lean4-lsp-mcp`):

```bash
npx lean4-lsp-mcp
# or
npm install -g lean4-lsp-mcp
lean-lsp-mcp
```

From a clone:

```bash
git clone https://github.com/r-irbe/lean4-lsp-mcp.git
cd lean4-lsp-mcp
npm install
npm run build
node dist/index.js
```

The server speaks MCP over stdio. Point your Lean 4 project at the process
working directory (or set `LEAN_PROJECT_ROOT`); `elan` / `lake` should be on `PATH`.

---

## 1. Key Capabilities (21 MCP Tools)

1. **Interactive Proof State & AltProof Advisor (`lean_goal`)**: Queries `$/lean/plainGoal` (`target: "tactic"` or `"filtered"`), `$/lean/plainTermGoal` (`target: "term"`), or the static/hybrid AltProof tactic & route advisor (`target: "altproof"`) via persistent `lake serve` broker sessions.
2. **Live Diagnostics & Abstract Interpretation (`lean_diagnostics`)**: Streams compiler elaboration errors, warnings, unsolved goals, and static abstract-interpretation certificates (`NatSubTruncation` on `a - b` without `b <= a`, `NatDivModByZero` on `/ d` without `0 < d`).
3. **Counterexample-First Proving (`lean_counterexample_search`)**: Synthesizes and runs an isolated Plausible property test outside the project root using Galois-pruned interval domains (`a <= 100`, `0 < d`, `a + b <= 100`) and AST threshold constants (`strategy: "slice" | "dense"`).
4. **Sub-5ms Offline `.ilean` Navigation (`lean_lookup_symbol`, `lean_decl_references`, `lean_module_hierarchy`, `lean_dependency_subgraph`)**: Direct binary/JSON parsing of `.lake/build/lib/**/*.ilean` files for instant jump-to-definition, declaration reference graphs (`uses` / `usedBy`), and module import/dependent DAGs without starting `lake serve`.
5. **Unified Multi-Source Search & Librarian Concordance (`lean_search`, `lean_book_index_lookup`, `lean_cross_itp_concordance`)**: Local ripgrep declaration search, Loogle, LeanSearch, Reservoir, arXiv, Kuzu knowledge graph, 65+ author-curated textbook indexes, and cross-prover tactic concordance (`lean4`, `coq`, `isabelle`, `hol_light`, `agda`).
6. **Metrics, Axiom Closure, Blueprints & C FFI (`lean_metrics`, `lean_module_census`, `lean_axiom_closure`, `lean_blueprint`, `lean_blueprint_scaffold`, `lean_proof_skeleton`, `lean_ffi`, `lean_exec`, `lean_resync`, `lean_server_status`)**: Project censuses, Milner Place-Link bigraph projections, `#print axioms` trust checks, PlasTeX Blueprint scaffolding, and C FFI sysroot inspection.

---

## 2. Architecture

```text
+-----------------------------------------------------------------------------+
|                          lean-lsp-mcp ARCHITECTURE                          |
+-----------------------------------------------------------------------------+
|                                                                             |
|  [ AI Host ] (Antigravity / Claude Code / Cursor / Windsurf / Copilot)      |
|       |                                                                     |
|  stdio JSON-RPC (MCP Protocol)                                              |
|       v                                                                     |
|  [ lean-lsp-mcp Server ]                                                    |
|    |-- Request Dispatcher, Alias Normalizer & LRU Search Cache              |
|    |-- .ilean Zero-Latency Indexer (Sub-5ms symbol & reference lookup)      |
|    |-- Abstract Interpreter (Interval/Zone/Octagon + AltProof Advisor)      |
|    |-- Plausible Counterexample Harness (Galois-pruned scratch runner)      |
|    |-- Lake Serve Broker Client (Multiplexed persistent FileWorkers)        |
|    |-- Clangd C FFI Sysroot Bridge (Injects `lean --print-prefix` headers)  |
|       |                                                                     |
|       +---> Lean 4 Toolchain (`lake serve` broker / `lake env lean`)        |
|       +---> Project Filesystem (`.lake/build/lib/**/*.ilean`, `.olean`)     |
|                                                                             |
+-----------------------------------------------------------------------------+
```

---

## 3. Tool Specifications & Agent Quick Reference

See [`instructions.md`](./instructions.md) for full copy-paste examples and parameter pitfall notes.

| Tool Name | Required Parameters | Key Optional Parameters |
| :--- | :--- | :--- |
| `lean_goal` | `filePath`, `line` (1-indexed) | `col` (1-indexed), `target` (`"tactic" \| "term" \| "filtered" \| "altproof"`), `hideTypeclasses`, `hideInaccessible`, `onlyTarget`, `goal`, `proof` |
| `lean_diagnostics` | `filePath` | `maxWaitMs` (default `4000`) |
| `lean_counterexample_search` | `filePath`, `theoremName` | `strategy` (`"slice" \| "dense"`), `samples` (default `100`), `budgetMs` (default `60000`), `imports` |
| `lean_exec` (alias `lean_run_code`) | `code` | `timeoutMs` (default `15000`) |
| `lean_resync` | `filePath` | *(none)* |
| `lean_server_status` | *(none)* | *(none)* |
| `lean_lookup_symbol` | `symbol` | *(none)* |
| `lean_decl_references` | `symbol` | `direction` (`"uses" \| "usedBy" \| "both"`), `limit` (default `50`) |
| `lean_module_hierarchy` | `moduleName` | `direction` (`"imports" \| "importedBy" \| "both"`), `transitive` (bool), `maxDepth` |
| `lean_dependency_subgraph` | `moduleName` | `maxDepth` (default `5`), `format` (`"mermaid" \| "dot" \| "json"`) |
| `lean_search` | `query` | `source` (`"code" \| "loogle" \| "ontology" \| "arxiv" \| "datasets" \| "reservoir" \| "book" \| "concordance" \| "symbol" \| "graph"`), `limit`, `prover`, `book` |
| `lean_book_index_lookup` | `term` (alias `query`) | `book` (corpus substring), `prover` (`"lean4" \| "coq" \| "isabelle" \| "hol_light"`) |
| `lean_cross_itp_concordance` | `concept` (alias `query`) | `source_prover`, `target_prover` |
| `lean_metrics` | `target` | `action` (`"census" \| "hierarchy" \| "subgraph" \| "bigraph" \| "axiom_audit" \| "altproof"`), `format`, `goal`, `proof` |
| `lean_module_census` | `targetPath` (alias `target`) | `format` (`"markdown" \| "json" \| "summary"`) |
| `lean_axiom_closure` | `symbol` | `module` (declaring module to import first) |
| `lean_blueprint` | *(none)* | `action` (`"status" \| "scaffold" \| "zettel" \| "skeleton" \| "walkthrough" \| "graph_neighborhood"`), `symbol`, `filePath`, `formalizationDir`, `blueprintDir` |
| `lean_blueprint_scaffold` | `symbol` | `filePath`, `line` |
| `lean_proof_skeleton` | `filePath` or `symbol` | *(none)* |
| `lean_ffi` | *(none)* | `action` (`"inspect_env" \| "resolve_symbol" \| "verify_headers" \| "sysroot"`), `externName`, `cHeaderPath` |

---

## 4. Configuration Across Agent Hosts

Prefer the published bin. After a local clone and `npm run build`, you can
also use `node dist/index.js`.

### Claude Code (`~/.claude/claude_desktop_config.json` or project `.mcp.json`)
```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "npx",
      "args": ["-y", "lean4-lsp-mcp"],
      "env": {
        "PATH": "${HOME}/.elan/bin:/usr/bin:/bin"
      }
    }
  }
}
```

### Choosing the project root

The server serves the project it is launched in. Root resolution is: the
`LEAN_PROJECT_ROOT` directory when set, else the launch directory when it holds
a Lake marker, else the nearest Lake root above it, else the launch directory
unchanged (never another project). Lake markers are `lakefile.lean`,
`lakefile.toml`, `lake-manifest.json`, and `packages/`; a directory with only
`lean-toolchain` is used as a last resort.

Pin the root explicitly when your host starts MCP servers from an unrelated
working directory:

```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "lean-lsp-mcp",
      "env": { "LEAN_PROJECT_ROOT": "/path/to/your/lake/project" }
    }
  }
}
```

`lakefile.toml` projects are fully supported (`lake env lean` is used for every
Lean invocation, so project modules are on `LEAN_PATH`). `lean_server_status`
reports the resolved root, how it was found, and the exact stdin invocation in
use.

### Cursor & Windsurf (`.cursor/mcp.json`)
```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "lean-lsp-mcp"
    }
  }
}
```

From a clone, after `npm run build`:

```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "node",
      "args": ["dist/index.js"]
    }
  }
}
```
