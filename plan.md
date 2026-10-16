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

## Next

- **W3**: editor-integration switch - consumers (the host editor's Lean
  rule directory) vendor this package's rules instead of their own copies.
- **W4**: harvest CLI port - the corpus census/harvest scripts call
  `lean-rules` instead of ad-hoc greps.
- npm publish (identity TBD; the package is publish-ready).

## Non-goals

- No behavior change to the existing MCP tools in rule releases.
- The declarative rules never import project-specific paths: the corpus is
  self-contained YAML consumable by any regex-based scanner.
