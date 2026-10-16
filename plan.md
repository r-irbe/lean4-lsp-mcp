# plan - lean4-lsp-mcp (the lean-analysis package)

Roadmap and shipped state. Design decisions and internal notes live in the
parent project's investigation garden; this file is the public-facing summary.

## Shipped

- **W1 (done)**: MCP server with 20 Lean tools (goal/term-goal, diagnostics
  stash via publishDiagnostics, axiom closure, loogle/search, book index,
  metrics, FFI, exec), public-readiness pass (generic docs, Apache-2.0,
  v0.3.0, exports map), EASCI-specific knowledge bases externalized
  (resolved via `.kuzu-config.json`, graceful when absent).
- **W2 (this release)**: `rules/` - the institutional declarative lint
  corpus (92 rules: tactic-redundancy family, 0-sorry / 0-axiom soundness
  pair, tier-DAG isolation guards, scaled-arithmetic and monolith-import
  conventions) + `lean-rules` (bin): a zero-build ESM runner over the YAML
  corpus - composite any/all conditions, Rust-inline-flag translation,
  RULE_COMPILE_WARNING instead of crashes, CI exit codes, severity floor.
  Fixture-tested (violation fixture trips the headline rules with exact
  lines; clean fixture zero).
- **W3 (done 2026-10-16)**: editor-integration switch - the parent
  project's Lean rule directory is generated state, synced one-way from
  this package's corpus; this corpus is canonical.
- **W4 (port landed 2026-10-16)**: `lean-harvest` (bin) - the TS port of
  the parent project's linter harvest script (parallel worker processes,
  per-file timeout, TSV/JSON output), with a test harness
  (`tests/test_harvest.mjs`).

## Next

- **W4 (adoption)**: the parent project's census/harvest scripts call
  `lean-harvest` once parity holds.
- npm publish (identity TBD; the package is publish-ready).

## Non-goals

- No behavior change to the existing MCP tools in rule releases.
- The declarative rules never import project-specific paths: the corpus is
  self-contained YAML consumable by any regex-based scanner.
