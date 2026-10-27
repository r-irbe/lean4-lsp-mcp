# Declarative Lean 4 AST-Grep & Lint Rules

This directory holds the 16 reusable declarative AST-grep / regex lint rules for Lean 4 formal verification projects. Use `lean-rules` (bundled with `lean4-lsp-mcp`) to scan `.lean` source files or directories against this rule catalog.

## Code vs prose (`scope`)

`lean-rules` matches a rule's regex against **masked code**: comments (`--`,
nested `/- ... -/`) and string literals are blanked out first, with newlines
preserved so line numbers are unchanged. A soundness rule therefore cannot fire
on a comment that *says* "No `sorry`, no `admit`" and cannot be blinded by a
`sorry` hiding inside a docstring.

A rule that genuinely targets prose opts in explicitly:

```yaml
scope: any      # match raw file text (comments and strings included)
```

Default is code-only. If you add a rule about comment markers or docstring
wording, set `scope: any`; otherwise leave it out.

## Rule Categories & Core Invariants

1. `rule-lean-no-uncertified-axiom`:
   - Enforces the 0-axiom sound verification invariant by flagging any ad-hoc `axiom` declaration.

2. `rule-lean-no-raw-float`:
   - Flags IEEE 754 raw hardware floats (`Float`, `Float32`, `Float64`) in formal specifications where exact integer, rational, or real arithmetic is expected.

3. `rule-lean-no-sorry-cheat`:
   - Flags `sorry`, `cheat`, or `admit` tactics in Lean source files, enforcing the 0-sorry verification invariant.

4. `rule-lean-no-unbounded-heartbeats`:
   - Flags `set_option maxHeartbeats 0` or limits exceeding 1,000,000 to prevent runaway CPU exhaustion and unbounded proof compilation stalls.

5. `rule-lean-max-import-depth`:
   - Flags deeply nested module imports (5 or more path segments) and direct imports into internal/private modules to protect modular encapsulation and build latency.

6. `rule-lean-p2m-card-conformance`:
   - Enforces lightweight theorem interface cards in `Theorems/` or `Interface/` that delegate proofs directly rather than inlining multi-step tactic scripts.

7. `rule-lean-no-trailing-tactic-semicolon`:
   - Flags redundant trailing semicolons in tactic scripts to prevent unconstrained elaborator sub-goals and fragile proof branching.

8. `rule-lean-no-redundant-idempotent-tactic`:
   - Consolidated parameterized rule flagging back-to-back identical idempotent tactic invocations (`simp`, `ring`, `omega`, `norm_num`, `decide`, `bv_decide`, `aesop`, `trivial`, `rfl`, `abel`, `linarith`, `positivity`, `funext`, `congr`, `ext`, `tauto`, `exact`, `assumption`, `contradiction`, `dsimp`, `push_neg`, `norm_cast`, `ring_nf`).

9. `rule-lean-no-unanchored-unfolding`:
   - Flags unanchored `dsimp` followed immediately by bare `simp` on complex function types, encouraging explicit `change` or `show` target horizons.

10. `rule-lean-no-unbounded-gevrey-norm`:
    - Flags unanchored Gevrey regularity norm manipulations without explicit analyticity radii or envelope ceilings.

11. `rule-lean-no-unbounded-logarithmic-gradient`:
    - Flags unanchored logarithmic gradient estimates without explicit Sobolev embedding constants.

12. `rule-lean-no-unbounded-piola-drift`:
    - Flags unanchored Piola coordinate deformations without Jacobian boundedness.

13. `rule-lean-no-unbounded-reynolds-stress`:
    - Flags unanchored Reynolds stress or turbulent cascade production without dissipation bounds.

14. `rule-lean-no-unbounded-swirl-amplification`:
    - Flags unanchored axisymmetric swirl amplification without critical bifurcation bounds.

15. `rule-lean-blueprint-annotation-hygiene`:
    - Enforces clean blueprint annotation formatting.

16. `rule-lean-pedagogical-docstring-quality`:
    - Flags vacuous docstrings that merely restate the declaration name without mathematical explanation.
