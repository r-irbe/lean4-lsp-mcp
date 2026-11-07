# Changelog

All notable changes to `lean4-lsp-mcp` are documented in this file.

## [0.7.0] - 2026-11-07

### Added
- **Live LSP navigation (`lean_navigate`, P1)**: Closed-enum semantic navigation tool covering `hover`, `definition`, `typeDefinition`, `declaration`, `implementation`, `references`, `documentSymbol`, `workspaceSymbol`, `findSymbol`, `prepareCallHierarchy`, `incomingCalls`, `outgoingCalls`, advertise-only `codeAction` (edits/commands stripped), offline `moduleImports`/`moduleImportedBy`, and zero-spawn `capabilities` introspection (`src/navigation.ts`, `src/index.ts`).
- **Spawn-free admitted-context gate & refusal taxonomy**: Hoisted admission currency checks (compiler stat identity, toolchain pin, `lake-manifest.json` SHA-256) and warm-route binding strictly above `ensureSession` broker/lock/analyzer/process spawn, with structured `environment_unavailable: <reasonCode>: <operation>: <detail>` refusals (`admission-missing`, `context-changed`, `live-identity-unavailable`, `ambiguous-warm-route`, `artifact-unavailable`, `bounds-exceeded`) and `LEAN_NAV_REQUIRE_EXACT=1` / `requireExactNavigation` strict mode.
- **Cold-open Lean 4 elaboration readiness**: `navigate()` waits on `$/lean/fileProgress` (`pending === 0`, tunable via `LEAN_NAV_READY_MS`) before querying live LSP methods and rejects premature null/empty replies on unfinished documents with `analysis_incomplete` rather than silent empty results.
- **Formal lifecycle verification (`formal/navigation-lifecycle/`)**: Instantiated `NavigationLifecycle.tla` for the MCP navigation & `.ilean` generation state machine alongside `NavLifecycleAsBuilt.cfg` and 4 mutant ratchets (`MutNavSpawnBeforeAdmission`, `MutNavLateCapture`, `MutNavNoBeforeReset`, `MutNavDropSurvivor`), verified offline in `tests/test_tla_navigation_lifecycle.mjs`.
- **Consolidated 22-rule `lean-rules` catalog (O6)**: Merged 6 distinct Lean rules (`lean-no-native-decide` including `decide +native`, `lean-classical-leak`, `lean-proof-length`, opt-in `lean-public-docstring-mandate`, `lean-simp-unbundle-hazard`, `lean-undergeneral-universe`), folded `lean-pure-scaled-arithmetic` metadata into `lean-no-raw-float`, and wired all 7 `*-test.yml` suites into `tests/test_rules_fixtures.mjs`.

### Changed
- **Admitted `.ilean` confinement, generation tracking & caps**: Confined `Lean4IleanIndex` scans under `realpathSync`-checked `moduleRoots`, added atomic `setLeanContext()` / `invalidate()` generation tracking plus rate-limited hit-path staleness refresh (`LEAN_ILEAN_CURRENCY_MS`), and raised default `LEAN_ILEAN_MAX_FILES` from `2048` to `65536`.
- **Elan hardlink & symlink shim resolution**: `resolveElanShim` in `src/project_root.ts` detects both symlinked and hardlinked (`dev+ino`) `~/.elan/bin/lean` shims and resolves them to the exact pinned toolchain binary, failing closed when the target toolchain is absent.
