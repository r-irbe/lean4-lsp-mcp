# USER_GUIDE.md - lean4-lsp-mcp Practical Manual

This guide covers installation, MCP host configuration, interactive proof state queries, static abstract-interpretation certificates, counterexample search, and CLI utilities (`lean-rules` and `lean-harvest`).

---

## 1. Prerequisites & Installation

- **Node.js**: `>= 22.6.0`
- **Lean 4 Toolchain**: `elan` and `lake` on `PATH` (optional for offline `.ilean` navigation and static analysis; required for live tactic goals and `lean_exec`)
- **ast-grep (`sg`)**: Optional, required only for the `lean-rules` structural linter CLI.

### Global or NPX Install

```bash
npm install -g lean4-lsp-mcp
# or run directly via npx:
npx -y lean4-lsp-mcp
```

### Build from Source

```bash
git clone https://github.com/r-irbe/lean4-lsp-mcp.git
cd lean4-lsp-mcp
npm install
npm run build
npm test
```

---

## 2. MCP Client Configuration

### Claude Code / Claude Desktop (`.mcp.json`)

```json
{
  "mcpServers": {
    "lean-lsp": {
      "command": "npx",
      "args": ["-y", "lean4-lsp-mcp"],
      "env": {
        "LEAN_PROJECT_ROOT": "/path/to/your/lean-project"
      }
    }
  }
}
```

### Cursor / Windsurf / Zed

Point the MCP command to `lean-lsp-mcp` (or `node /path/to/lean4-lsp-mcp/dist/index.js`) and set `LEAN_PROJECT_ROOT` to your Lake workspace directory containing `lakefile.lean` or `lakefile.toml`.

---

## 3. Core Workflows across the 21 MCP Tools

### 3.1 Interactive Proof State & AltProof Advisor (`lean_goal`)

Query tactic goals, term goals, filtered hypothesis views, or ranked tactic recommendations at a 1-indexed `(line, col)` cursor position:

```json
{
  "filePath": "MyProject/Basic.lean",
  "line": 42,
  "col": 4,
  "target": "tactic"
}
```

Set `"target": "altproof"` to run the hybrid abstract interpreter and receive ranked tactic routes (`omega`, `linarith`, `ring`, `simp`, `exact?`, or induction templates).

### 3.2 Live Diagnostics & Static Certificates (`lean_diagnostics`)

```json
{
  "filePath": "MyProject/Basic.lean",
  "maxWaitMs": 4000
}
```

In addition to Lean compiler diagnostics, `lean_diagnostics` runs the WebAssembly abstract interpreter (`lean_analyzer.wasm`) to emit static certificates for:
- `NatSubTruncation`: truncating subtraction `a - b` on `Nat` without a guard `b <= a`.
- `NatDivModByZero`: division or modulo `a / d` or `a % d` without `0 < d`.

### 3.3 Counterexample-First Proving (`lean_counterexample_search`)

Before spending tactic turns on a conjecture, test whether it is falsifiable:

```json
{
  "filePath": "MyProject/Conjectures.lean",
  "theoremName": "my_conjecture",
  "strategy": "dense"
}
```

### 3.4 Sub-5ms Offline `.ilean` Navigation

When `.lake/build/lib/**/*.ilean` files exist, navigate the project without spawning `lake serve`:
- `lean_lookup_symbol`: `{"symbol": "MyProject.my_theorem"}`
- `lean_decl_references`: `{"symbol": "MyProject.my_theorem", "direction": "both"}`
- `lean_module_hierarchy`: `{"moduleName": "MyProject.Basic", "direction": "both"}`
- `lean_dependency_subgraph`: `{"moduleName": "MyProject.Basic", "format": "mermaid"}`

### 3.5 Multi-Source Search & Cross-ITP Concordance

- `lean_search`: Query local declarations (`source: "code"`), Loogle (`"loogle"`), ITP ontology (`"ontology"`), Lean Reservoir (`"reservoir"`), arXiv (`"arxiv"`), textbook indexes (`"book"`), or Kuzu graph (`"graph"`).
- `lean_book_index_lookup`: Search 65+ theorem-proving textbook indexes (`{"term": "galois connection"}`).
- `lean_cross_itp_concordance`: Translate proof idioms across Coq, Isabelle/HOL, HOL Light, and Lean 4 (`{"concept": "induction", "source_prover": "coq", "target_prover": "lean4"}`).

### 3.6 Audits, Blueprints, and C FFI

- `lean_axiom_closure`: Run `#print axioms` on a declaration (`{"symbol": "MyProject.my_theorem"}`).
- `lean_module_census` / `lean_metrics`: Count declarations, theorems, definitions, and proof density across modules.
- `lean_blueprint` / `lean_blueprint_scaffold` / `lean_proof_skeleton`: Generate PlasTeX Blueprint nodes, proof skeletons, and walkthroughs.
- `lean_ffi`: Inspect `@[extern]` C FFI bindings and Lean sysroot headers.

---

## 4. Bundled CLI Utilities

### `lean-rules` (Structural AST-Grep Linter)

Scans Lean 4 files against the 22 bundled `ast-grep` rules in `rules/`:

```bash
npx lean-rules scan MyProject/
npx lean-rules test
```

### `lean-harvest` (Parallel Linter Harvester)

Runs `lake env lean -D<flag>=true` across a worker pool and outputs a TSV or JSON report:

```bash
npx lean-harvest findings.tsv "linter.unusedVariables linter.unusedTactic"
```
