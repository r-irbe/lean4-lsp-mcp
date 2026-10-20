# Declarative Lean 4 AST-Grep & Lint Rules

This directory holds reusable declarative AST-grep / regex lint rules for Lean 4 formal verification projects. Use `lean-rules` (bundled with `lean4-lsp-mcp`) to scan `.lean` source files or directories against this rule catalog.

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

8. `rule-lean-no-redundant-have`:
   - Flags consecutive anonymous `have :` hypotheses that shadow local definitions and pollute proof state contexts.

9. `rule-lean-no-redundant-open`:
   - Flags consecutive duplicate `open` namespace declarations that introduce redundant scope pollution and non-deterministic symbol resolution.

10. `rule-lean-no-redundant-simp-all`:
    - Flags consecutive or unconstrained `simp_all` tactics to prevent runaway elaborator loops and proof context pollution.

11. `rule-lean-no-redundant-ring`:
    - Flags consecutive duplicate `ring` tactic calls that introduce redundant polynomial normalization cycles and clutter proof scripts.

12. `rule-lean-no-redundant-linarith`:
    - Flags consecutive duplicate `linarith` tactic calls that introduce redundant Fourier-Motzkin linear arithmetic normalizer cycles and clutter proof scripts.

13. `rule-lean-no-redundant-positivity`:
    - Flags consecutive duplicate `positivity` tactic calls that introduce redundant numerical non-negativity extension passes and clutter proof scripts.

14. `rule-lean-no-redundant-omega`:
    - Flags consecutive duplicate `omega` tactic calls that introduce redundant Presburger arithmetic normalizer cycles and clutter proof scripts.

15. `rule-lean-no-redundant-norm-num`:
    - Flags consecutive duplicate `norm_num` tactic calls that introduce redundant numerical normalization cycles and clutter proof scripts.

16. `rule-lean-no-redundant-simp`:
    - Flags consecutive duplicate `simp` tactic calls that introduce redundant simplifier cycles and bloat elaboration traces.

17. `rule-lean-no-redundant-ring-nf`:
    - Flags consecutive duplicate `ring_nf` tactic calls that introduce redundant ring normal form reduction cycles and bloat proof traces.

18. `rule-lean-no-redundant-ext`:
    - Flags consecutive duplicate `ext` tactic calls that introduce redundant extensionality reductions and clutter proof scripts.

19. `rule-lean-no-unanchored-unfolding`:
    - Flags unanchored `dsimp` followed immediately by bare `simp` on complex function types, encouraging explicit `change` or `show` target horizons.

20. `rule-lean-no-redundant-tauto`:
    - Flags consecutive duplicate `tauto` tactic calls that introduce redundant propositional tautology searches and clutter proof scripts.

21. `rule-lean-no-redundant-decide`:
    - Flags consecutive duplicate `decide` tactic calls that introduce redundant computational reflection evaluations and clutter proof scripts.

22. `rule-lean-no-redundant-simp-only`:
    - Flags consecutive duplicate `simp only` tactic calls that introduce redundant simplifier cycles and bloat elaboration traces.

23. `rule-lean-no-redundant-dsimp`:
    - Flags consecutive duplicate `dsimp` tactic calls that introduce redundant definitional simplifier cycles and bloat elaboration traces.

24. `rule-lean-blueprint-annotation-hygiene`:
    - Flags top-level landmark theorems missing descriptive mathematical docstrings or blueprint metadata for graph rendering.

25. `rule-lean-pedagogical-docstring-quality`:
    - Flags vacuous or tautological docstrings on declarations, enforcing mathematical intuition and explanatory quality.

37. `rule-lean-no-redundant-simp-all-dup`:
   - Flags consecutive duplicate `simp_all` calls that introduce redundant context simplification cycles and bloat elaboration traces.

38. `rule-lean-no-redundant-constructor`:
   - Flags consecutive duplicate `constructor` calls that introduce dead elaboration cycles and unconstrained subgoals.

39. `rule-lean-no-redundant-cases`:
   - Flags consecutive duplicate `cases` calls that introduce dead elaboration cycles and unconstrained subgoals.

40. `rule-lean-no-redundant-rewrite`:
   - Flags consecutive duplicate `rw` tactic calls that introduce redundant rewrite passes and clutter proof scripts.

41. `rule-lean-no-redundant-funext`:
   - Flags consecutive duplicate `funext` calls that introduce redundant extensionality reductions and clutter proof scripts.

42. `rule-lean-no-redundant-simp-args`:
   - Flags duplicate theorem or lemma arguments inside a simp bracket list to prevent redundant simplifier index lookups and inflated AST proof payloads.

43. `rule-lean-no-redundant-unfold`:
   - Flags consecutive duplicate `unfold` calls on identical declarations to prevent redundant definitional unfolding passes and bloated proof AST payloads.

44. `rule-lean-no-redundant-exact`:
   - Flags consecutive duplicate `exact` calls on identical declarations or hypotheses to prevent redundant proof terms and dead elaboration cycles.

45. `rule-lean-no-redundant-simp-dup`:
   - Flags consecutive duplicate `simp` calls on identical argument sets to prevent redundant simplifier reduction cycles and bloated proof AST traces.

46. `rule-lean-no-redundant-rw-dup`:
   - Flags consecutive duplicate `rw` calls on identical rewrite lemmas or hypotheses to prevent redundant equational substitution cycles and dead elaboration steps.

47. `rule-lean-no-redundant-have-dup`:
   - Flags consecutive duplicate `have` assertions on identical variable names without consuming them to prevent shadowed local context entries and bloated proof AST traces.

48. `rule-lean-no-redundant-intros-dup`:
   - Flags consecutive duplicate `intro` or `intros` invocations without intermediate tactic operations to prevent shadowed binder churn and bloated proof AST traces.

49. `rule-lean-no-redundant-rfl-dup`:
   - Flags consecutive duplicate `rfl` calls that introduce redundant reflexivity reduction cycles and bloat elaboration traces.

50. `rule-lean-no-redundant-trivial-dup`:
   - Flags consecutive duplicate `trivial` calls that introduce redundant decision reduction cycles and bloat elaboration traces.

51. `rule-lean-no-redundant-assumption-dup`:
   - Flags consecutive duplicate `assumption` calls that introduce redundant hypothesis search cycles and bloat elaboration traces.

52. `rule-lean-no-redundant-split-dup`:
   - Flags consecutive duplicate `split` calls that introduce redundant case branching cycles and bloat elaboration traces.

53. `rule-lean-no-redundant-clear-dup`:
   - Flags consecutive duplicate `clear` calls that introduce redundant hypothesis removal cycles and bloat elaboration traces.

54. `rule-lean-no-redundant-revert-dup`:
   - Flags consecutive duplicate `revert` calls that introduce redundant binder re-generalization cycles and bloat elaboration traces.

55. `rule-lean-no-redundant-generalize-dup`:
   - Flags consecutive duplicate `generalize` calls that introduce redundant hypothesis generalization churn, context bloat, and fragile goal states.

56. `rule-lean-no-redundant-subst-dup`:
   - Flags consecutive duplicate `subst` calls that introduce redundant equality substitution churn, variable rebinding overhead, and fragile goal states.

57. `rule-lean-no-redundant-change-dup`:
   - Flags consecutive duplicate `change` calls that introduce redundant definitional rewrite churn, type horizon recalculation overhead, and bloated proof AST traces.

58. `rule-lean-no-redundant-show-dup`:
   - Flags consecutive duplicate `show` calls that introduce redundant goal restatement churn, type horizon recalculation overhead, and bloated proof AST traces.

59. `rule-lean-no-redundant-suffices-dup`:
   - Flags consecutive duplicate `suffices` calls that introduce redundant backward proof obligations, context duplication overhead, and bloated proof AST traces.

60. `rule-lean-no-redundant-dsimp-only`:
   - Flags consecutive duplicate `dsimp only` calls that introduce redundant definitional simplifier cycles, type horizon recalculation overhead, and bloated proof AST traces.

61. `rule-lean-no-redundant-rcases-dup`:
   - Flags consecutive duplicate `rcases` calls that introduce redundant pattern destructuring churn, bloated proof state, and unconstrained AST traces.

62. `rule-lean-no-redundant-simp-only-dup`:
   - Flags consecutive duplicate `simp only` calls that introduce redundant simplifier passes, cache invalidation, and slow elaborator traversals.

63. `rule-lean-no-redundant-dsimp-only-dup`:
   - Flags consecutive duplicate `dsimp only` calls that introduce redundant definitional simplifier engine passes, cache invalidation, and slow elaborator traversals.

64. `rule-lean-no-redundant-apply-dup`:
   - Flags consecutive duplicate `apply` calls that introduce redundant unification passes, backtrack overhead, and slow elaborator traversals.

65. `rule-lean-no-redundant-intros-dup`:
   - Flags consecutive duplicate `intros` calls that introduce redundant binder introduction cycles, variable scope churn, and slow elaborator traversals.

66. `rule-lean-no-redundant-simp-dup`:
   - Flags consecutive duplicate `simp` calls that introduce redundant simplifier passes, duplicate congruence lemma traversals, and unnecessary proof term bloat.

67. `rule-lean-no-redundant-simp-all-dup`:
   - Flags consecutive duplicate `simp_all` calls that introduce redundant context simplification cycles, elaborator pollution, and runaway trace bloat.

68. `rule-lean-no-redundant-constructor-dup`:
   - Flags consecutive duplicate `constructor` calls that introduce dead elaboration cycles, unconstrained subgoals, and runaway proof trace bloat.

69. `rule-lean-no-redundant-cases-dup`:
   - Flags consecutive duplicate `cases` calls that introduce redundant case splits, elaborator context churn, and bloated proof trees.

70. `rule-lean-no-redundant-rename-i-dup`:
   - Flags consecutive duplicate `rename_i` calls that introduce dead binder renaming cycles, context pollution, and slow elaborator traversals.

71. `rule-lean-no-redundant-unfold-dup`:
   - Flags consecutive duplicate `unfold` calls that introduce redundant definition unfolding passes, cache invalidation, and bloated proof trees.

72. `rule-lean-no-redundant-simp-target-dup`:
   - Flags consecutive duplicate `simp` invocations targeting the main goal without intermediate premise modification or discharge, preventing redundant simplifier passes and elaboration trace inflation.

73. `rule-lean-no-redundant-rw-target-dup`:
   - Flags consecutive duplicate `rw` invocations targeting the main goal with identical rewrite arguments, preventing redundant equational substitutions and elaborator latency inflation.

74. `rule-lean-no-redundant-clear-target-dup`:
   - Flags consecutive duplicate `clear` invocations targeting the identical hypothesis identifier, preventing dead hypothesis search cycles and elaborator context churn.

75. `rule-lean-no-redundant-revert-target-dup`:
   - Flags consecutive duplicate `revert` invocations targeting the identical hypothesis identifier, preventing redundant binder reintroduction cycles, hypothesis context churn, and elaborator trace bloat.

76. `rule-lean-no-redundant-generalize-target-dup`:
   - Flags consecutive duplicate `generalize` invocations targeting the identical expression or identifier, preventing redundant generalized equality introductions, hypothesis context churn, and elaborator trace bloat.

77. `rule-lean-no-redundant-specialize-target-dup`:
   - Flags consecutive duplicate `specialize` invocations targeting the identical hypothesis or identifier without intermediate term modification, preventing redundant instantiation cycles, hypothesis context pollution, and elaborator trace bloat.

78. `rule-lean-no-redundant-obtain-target-dup`:
   - Flags consecutive duplicate `obtain` invocations targeting the identical term or binder pattern without intermediate premise discharge, preventing redundant existential destructuring passes, hypothesis context churn, and elaborator trace bloat.

79. `rule-lean-no-redundant-rcases-target-dup`:
   - Flags consecutive duplicate `rcases` invocations targeting the identical term or pattern without intermediate premise modification, preventing redundant recursive destructuring passes, hypothesis context churn, and elaborator trace bloat.

80. `rule-lean-no-redundant-cases-target-dup`:
   - Flags consecutive duplicate `cases` invocations targeting the identical term or hypothesis identifier without intermediate case elimination, preventing redundant case splits, hypothesis context churn, and elaborator trace bloat.

81. `rule-lean-no-redundant-subst-target-dup`:
   - Flags consecutive duplicate `subst` invocations targeting the identical variable or hypothesis without intermediate equality derivation, preventing redundant substitution passes, hypothesis context churn, and elaborator trace bloat.

82. `rule-lean-no-redundant-congr-target-dup`:
   - Flags consecutive duplicate `congr` invocations targeting identical terms or applications without intermediate goal simplification, preventing redundant congruence passes, goal tree fragmentation, and elaborator trace bloat.





