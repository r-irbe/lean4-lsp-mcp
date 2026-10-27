import Lake
open Lake DSL

package lean_analyzer where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib LeanAnalyzer where
  roots := #[`LeanAnalyzer.AbstractInterpretation]
