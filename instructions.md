# lean-lsp (lean4-lsp-mcp): AI Agent Instructions & Tool Reference

> **Purpose**: High-speed interactive Lean 4 proving, sub-millisecond `.ilean` navigation, semantic + literature search, counterexample falsification, AltProof tactic advising, and certified axiom auditing.
> **Golden Rule**: NEVER edit a `.lean` file with `trace_state` or run a slow `lake build` loop just to inspect a proof state or look up a symbol. Use `lean_goal`, `lean_diagnostics`, `lean_lookup_symbol`, and `lean_search` first.

---

## 1. Quick Decision Matrix: Which Tool to Call?

| Task | Tool to Call | Latency | Requires `lake serve`? |
| :--- | :--- | :--- | :--- |
| Inspect live tactic proof state (`|- ...`) at cursor | `lean_goal` (`target: "tactic"` or `"filtered"`) | ~50-200 ms | Yes (auto-managed via broker) |
| Inspect expected type of a hole `_` or subterm | `lean_goal` (`target: "term"`) | ~50-200 ms | Yes |
| Get ranked tactic advice, route hints, & static abstract-interpretation certificates (`NatSubTruncation`, `NatDivModByZero`) | `lean_goal` (`target: "altproof"`) or `lean_metrics` (`action: "altproof"`) | < 10 ms (offline) / ~100 ms (live) | Optional |
| Get all compiler errors, warnings, & unsolved goals for a file | `lean_diagnostics` | ~100-500 ms | Yes |
| Test if a theorem statement is false before proving it | `lean_counterexample_search` | ~2-15 s | No (isolated scratch process) |
| Find where a theorem/def/structure is defined (file & line) | `lean_lookup_symbol` | < 5 ms | **No** (reads `.ilean` cache) |
| Find what constants a declaration uses or what uses it | `lean_decl_references` | < 5 ms | **No** (reads `.ilean` cache) |
| Check module imports or reverse `importedBy` blast radius | `lean_module_hierarchy` or `lean_metrics` (`action: "hierarchy"`) | < 5 ms | **No** (reads `.ilean` cache) |
| Search local declarations, Loogle, LeanSearch, Reservoir, arXiv, or ITP Ontology | `lean_search` (`source: "code" | "loogle" | "ontology" | "reservoir" | "arxiv" | "book" | "concordance" | "graph"`) | < 20 ms (local) | **No** |
| Look up a concept in author-curated textbook indexes (Cousot, Pierce SF, Chlipala CPDT, Nipkow, Harrison, etc.) | `lean_book_index_lookup` | < 10 ms | **No** |
| Translate a proof concept or tactic across Lean 4, Coq/Rocq, Isabelle, HOL Light, Agda | `lean_cross_itp_concordance` | < 10 ms | **No** |
| Verify a theorem depends only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`) | `lean_axiom_closure` (single symbol) or `lean_metrics` (`action: "axiom_audit"`, directory/file) | ~1-3 s / < 50 ms | **No** |
| Run a quick standalone `#check`, `#eval`, or `#synth` snippet without touching files | `lean_exec` | ~1-3 s | **No** (`lean --stdin`) |
| Audit Lean Blueprint coverage (`\leanok`, `\uses`), generate LaTeX scaffolds, or Layer-4 Zettels | `lean_blueprint` (`action: "status" | "scaffold" | "zettel" | "skeleton" | "walkthrough" | "graph_neighborhood"`) | < 100 ms | **No** |
| Recover when live goals look stale after an external file edit | `lean_resync` (or `lean_server_status` to inspect workers) | ~50 ms | Yes |

---

## 2. How to Invoke in Antigravity (`call_mcp_tool`)

All `lean-lsp` tools are registered under `ServerName: "lean-lsp"`. Call them via `call_mcp_tool`:

```json
{
  "ServerName": "lean-lsp",
  "ToolName": "lean_goal",
  "Arguments": {
    "filePath": "docs/easci/lean/EASCI/QualityGates.lean",
    "line": 42,
    "col": 5,
    "target": "filtered"
  }
}
```

---

## 3. Exact Parameter Signatures & Copy-Paste Examples (All 21 Tools)

### 3.1 Interactive Proving & Diagnostics

#### `lean_goal`
Queries tactic goals, filtered goals, expected term types, or the AltProof advisor.
- **Required**: `filePath` (string), `line` (integer, **1-indexed**).
- **Optional**:
  - `col` (integer, **1-indexed**, default `1`; alias: `character`)
  - `target` (`"tactic" | "term" | "filtered" | "altproof"`, default `"tactic"`)
  - `filter` (`"all" | "hypotheses" | "target"`)
  - `hideTypeclasses` (boolean), `hideInaccessible` (boolean), `onlyTarget` (boolean), `maxGoals` (integer, default `3`)
  - `goal` (string, explicit goal text for offline `target: "altproof"`), `proof` (string, proof block for `target: "altproof"`), `format` (`"markdown" | "json"`)
- **Cursor Rule**: Place `line` inside the `by` block (on a tactic line or `sorry`), **never** on line 1 or the `theorem` header (headers return `no goals`).
- **Examples**:
  ```json
  {"filePath": "docs/easci/lean/EASCI/Tactics.lean", "line": 120, "col": 3, "target": "filtered"}
  {"filePath": "docs/easci/lean/EASCI/Tactics.lean", "line": 120, "col": 12, "target": "term"}
  {"filePath": "docs/easci/lean/EASCI/Tactics.lean", "line": 120, "target": "altproof", "goal": "a + b <= 100"}
  ```

#### `lean_diagnostics`
Returns live compiler elaboration errors, warnings, unsolved goals, AND static abstract-interpretation certificates (`NatSubTruncation` for `a - b` without `b <= a`, `NatDivModByZero` for `/ d` without `0 < d`).
- **Required**: `filePath` (string).
- **Optional**: `maxWaitMs` (integer, default `4000`).
- **Example**:
  ```json
  {"filePath": "docs/easci/lean/EASCI/QualityGates.lean", "maxWaitMs": 4000}
  ```

#### `lean_counterexample_search`
Synthesizes and executes a Plausible property test in an isolated scratch directory outside the repo (never touches zero-sorry gates), with automatic Galois-guided interval domain pruning (`a <= 100`, `0 < d`, `a + b <= 100`) and AST threshold constant extraction.
- **Required**: `filePath` (string), `theoremName` (string, bare or qualified name).
- **Optional**:
  - `samples` (integer, default `100`, max `10000`)
  - `budgetMs` (integer, default `60000`, max `120000`)
  - `strategy` (`"slice" | "dense"`, default `"slice"`; use `"dense"` to probe multiple size schedules and binder orders)
  - `probeBudgetMs` (integer, default `15000`)
  - `imports` (array of strings, e.g. `["EASCI.Testing.Samplers"]`)
- **Example**:
  ```json
  {"filePath": "docs/easci/lean/EASCI/QualityGates.lean", "theoremName": "gate_monotone", "strategy": "dense", "samples": 200}
  ```

#### `lean_exec` (and legacy alias `lean_run_code`)
Runs standalone Lean 4 code via `lake env lean --stdin` without creating temporary files.
- **Required**: `code` (string).
- **Optional**: `timeoutMs` (integer, default `15000`).
- **Example**:
  ```json
  {"code": "import Mathlib.Data.Nat.Basic
#check Nat.sub_add_cancel"}
  ```

#### `lean_resync` & `lean_server_status`
- `lean_resync`: `{"filePath": "docs/easci/lean/EASCI/QualityGates.lean"}`: forces disk re-read and `textDocument/didChange` bump when goals look stale after external edits.
- `lean_server_status`: `{}`: reports active `lake serve` broker attachment, project root, open files, and worker RSS memory.

---

### 3.2 Offline `.ilean` Navigation & Dependency DAG (< 5 ms, No `lake serve` Required)

#### `lean_lookup_symbol`
Finds exact file path, 1-based line/column range, and declaring module for any compiled declaration.
- **Required**: `symbol` (string).
- **Example**:
  ```json
  {"symbol": "EASCI.QualityGates.GateConfig"}
  ```

#### `lean_decl_references`
Queries the `.ilean` declaration reference graph: which constants `symbol` uses (`uses`), and which declarations use `symbol` (`usedBy`).
- **Required**: `symbol` (string).
- **Optional**: `direction` (`"uses" | "usedBy" | "both"`, default `"both"`), `limit` (integer, default `50`).
- **Example**:
  ```json
  {"symbol": "EASCI.QualityGates.gatePass", "direction": "usedBy", "limit": 25}
  ```

#### `lean_module_hierarchy`
Traverses the module import DAG (`imports` / `importedBy`) with cycle detection. Always run `direction: "importedBy"` before changing a public signature!
- **Required**: `moduleName` (string, dot-separated, e.g. `"EASCI.Tactics"`).
- **Optional**: `direction` (`"imports" | "importedBy" | "both"`, default `"both"`), `transitive` (boolean, default `false`), `maxDepth` (integer, default `20`).
- **Example**:
  ```json
  {"moduleName": "EASCI.QualityGates", "direction": "importedBy", "transitive": true}
  ```

#### `lean_dependency_subgraph`
Renders the import subgraph around a module in Mermaid, DOT, or JSON.
- **Required**: `moduleName` (string).
- **Optional**: `maxDepth` (integer, default `5`), `format` (`"mermaid" | "dot" | "json"`, default `"mermaid"`).
- **Example**:
  ```json
  {"moduleName": "EASCI.StochasticCCV.StageMatrix5", "maxDepth": 3, "format": "mermaid"}
  ```

---

### 3.3 Unified Search, Book Indexes & Cross-ITP Concordance

#### `lean_search`
Unified multi-source search dispatcher.
- **Required**: `query` (string).
- **Optional**:
  - `source` (`"code" | "loogle" | "ontology" | "arxiv" | "datasets" | "reservoir" | "book" | "concordance" | "symbol" | "graph" | "local"`, default `"code"`)
  - `limit` (integer, default `10`)
  - `prover` (string, e.g. `"lean4"`, `"coq"`, `"isabelle"`, `"hol_light"`)
  - `source_prover` (string), `target_prover` (string)
  - `book` (string, substring filter on book corpus ID)
  - `category` (string, arXiv category e.g. `"cs.LO"`, `"math.CT"`)
- **Examples**:
  ```json
  {"query": "Finset.sum_le_sum", "source": "code", "limit": 10}
  {"query": "?a - ?b + ?b = ?a", "source": "loogle"}
  {"query": "Galois connection", "source": "ontology", "prover": "lean4"}
  {"query": "weak topological ordering", "source": "book", "book": "cousot"}
  ```

#### `lean_book_index_lookup`
Direct lookup in the 65+ author-curated textbook & monograph back-of-the-book indexes (`docs/investigation-garden/source-materials/indexes/*.index.json`).
- **Required**: `term` (string). **NOTE**: the parameter name is `term`, NOT `query`!
- **Optional**: `book` (string, e.g. `"cousot"`, `"pierce"`, `"chlipala"`), `prover` (string, e.g. `"lean4"`, `"coq"`, `"isabelle"`, `"hol_light"`).
- **Example**:
  ```json
  {"term": "octagon domain", "book": "cousot-abstract-interpretation-2021"}
  ```

#### `lean_cross_itp_concordance`
Maps concepts, tactics, and idioms across prover families (`lean4`, `coq`, `isabelle`, `hol_light`, `agda`, `metamath`).
- **Required**: `concept` (string). **NOTE**: the parameter name is `concept`, NOT `query`!
- **Optional**: `source_prover` (string), `target_prover` (string).
- **Example**:
  ```json
  {"concept": "generalizing induction", "source_prover": "coq", "target_prover": "lean4"}
  ```

---

### 3.4 Metrics, AltProof, Blueprints, Zettels, Axioms & FFI

#### `lean_metrics`
Consolidated project/module metrics, architecture projections, and AltProof analysis.
- **Required**: `target` (string: file path, directory path, module name, or goal string).
- **Optional**:
  - `action` (`"census" | "hierarchy" | "subgraph" | "bigraph" | "axiom_audit" | "altproof"`, default `"census"`)
  - `format` (`"markdown" | "json" | "summary" | "mermaid" | "dot"`, default `"markdown"`)
  - `goal` (string, for `action: "altproof"`), `proof` (string, for `action: "altproof"`)
  - `direction` (`"imports" | "importedBy" | "both"`), `transitive` (boolean), `maxDepth` (integer)
- **Examples**:
  ```json
  {"target": "docs/easci/lean/EASCI/Foundations/CS", "action": "census", "format": "summary"}
  {"target": "docs/easci/lean/EASCI/Foundations/CS", "action": "axiom_audit"}
  {"target": "docs/easci/lean/EASCI/QualityGates.lean", "action": "altproof", "goal": "g1 <= g2"}
  ```

#### `lean_module_census`
Direct declaration census over a directory or `.lean` file.
- **Required**: `targetPath` (string).
- **Example**:
  ```json
  {"targetPath": "docs/easci/lean/EASCI/Epistemics"}
  ```

#### `lean_axiom_closure`
Runs `#print axioms <symbol>` via `lake env lean --stdin` to verify zero `sorryAx` or non-standard axioms in the transitive closure.
- **Required**: `symbol` (string).
- **Optional**: `module` (string, declaring module to import first, e.g. `"EASCI.QualityGates"`).
- **Example**:
  ```json
  {"symbol": "EASCI.Foundations.CS.AbstractInterpretation.OctagonBound.sum_diff_double_bound", "module": "EASCI.Foundations.CS.AbstractInterpretation"}
  ```

#### `lean_blueprint` (plus specialized `lean_blueprint_scaffold` and `lean_proof_skeleton`)
Audits Lean Blueprint alignment or generates LaTeX blueprint macros, proof skeletons, pedagogical walkthroughs, and Layer-4 Zettels.
- **Optional / Context-dependent**:
  - `action` (`"status" | "scaffold" | "zettel" | "skeleton" | "walkthrough" | "graph_neighborhood"`, default `"status"`)
  - `symbol` (string, required for `scaffold`, `zettel`, `walkthrough`)
  - `filePath` (string, required for `skeleton` if `symbol` omitted)
  - `sectionId` (string, required for `graph_neighborhood`)
  - `formalizationDir` (string), `blueprintDir` (string), `outputPath` (string), `format` (`"markdown" | "json" | "summary"`)
- **Examples**:
  ```json
  {"action": "status", "formalizationDir": "docs/easci/lean/EASCI", "blueprintDir": "docs/easci/lean/blueprint/src", "format": "summary"}
  {"action": "scaffold", "symbol": "EASCI.QualityGates.gate_monotone"}
  {"action": "skeleton", "filePath": "docs/easci/lean/EASCI/QualityGates.lean", "symbol": "gate_monotone"}
  ```

#### `lean_ffi`
Inspects Lean 4 C FFI `@[extern]` bindings, C headers, and `lean --print-prefix` sysroot flags.
- **Optional**: `action` (`"inspect_env" | "resolve_symbol" | "verify_headers" | "sysroot"`, default `"inspect_env"`), `externName` (string), `cHeaderPath` (string).

---

## 4. Top 5 Parameter Pitfalls to Avoid

1. **Wrong parameter name in `lean_book_index_lookup` and `lean_cross_itp_concordance`**:
   - `lean_book_index_lookup` requires `term` (NOT `query`, and `prover`, NOT `prover_filter`).
   - `lean_cross_itp_concordance` requires `concept` (NOT `query`).
   - If you prefer passing `query`, call `lean_search` with `source: "book"` or `source: "concordance"` (which accepts `query`, `term`, or `concept` interchangeably).
2. **1-Indexed Line and Column Numbers**:
   - `lean_goal` uses **1-based** `line` and `col` (or `character`). Never pass 0-based coordinates.
3. **Querying `lean_goal` on Theorem Headers**:
   - Querying `lean_goal` on the `theorem foo ... :=` header line returns `no goals`. Always pass the line number **inside** the `by` block (on the first tactic line or on `sorry`).
4. **Inaccessible Dagger Variables (`x+` / `h+`)**:
   - Use `lean_goal` with `target: "filtered"` (or `hideInaccessible: false` to see them) and bind inaccessible variables explicitly via `rename_i` or `rcases` before referencing them in tactics.
5. **Passing `module` to `lean_axiom_closure`**:
   - Always pass `"module": "<DeclaringModule>"` alongside `"symbol": "<FullSymbolName>"` so `lean --stdin` imports the compiled `.olean` before running `#print axioms`.
