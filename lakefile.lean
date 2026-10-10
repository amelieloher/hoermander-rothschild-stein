import Lake

open Lake DSL

package «hormander» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.deprecated, true⟩
]

@[default_target]
lean_lib «Hormander» where
  globs := #[.andSubmodules `Hormander]
  leanOptions := projectLeanOptions

/-- The Rothschild–Stein theory, Baker–Campbell–Hausdorff, Chow–Rashevskii and Nagel–Stein–Wainger. -/
@[default_target]
lean_lib «RothschildStein» where
  globs := #[.andSubmodules `RothschildStein]
  leanOptions := projectLeanOptions

/-- Heat kernel, Gaussian bounds, Poincaré and Harnack inequalities for sub-Laplacians on Carnot groups. -/
@[default_target]
lean_lib «HeatKernel» where
  globs := #[.andSubmodules `HeatKernel]
  leanOptions := projectLeanOptions


/-- Comparator configuration `comparators/Hormander`: Mathlib-only statements, one intentional
`sorry` per theorem. -/
@[default_target]
lean_lib «HormanderChallenge» where
  roots := #[`comparators.Hormander.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/Hormander` statements proved from the library. -/
@[default_target]
lean_lib «HormanderSolution» where
  roots := #[`comparators.Hormander.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/RothschildStein`: Mathlib-only statements, one
intentional `sorry` per theorem. -/
@[default_target]
lean_lib «RothschildSteinChallenge» where
  roots := #[`comparators.RothschildStein.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/RothschildStein` statements proved from the library. -/
@[default_target]
lean_lib «RothschildSteinSolution» where
  roots := #[`comparators.RothschildStein.Solution]
  leanOptions := projectLeanOptions

/-- Comparator configuration `comparators/HeatKernel`: Mathlib-only statements, one intentional
`sorry` per theorem. -/
@[default_target]
lean_lib «HeatKernelChallenge» where
  roots := #[`comparators.HeatKernel.Challenge]
  leanOptions := projectLeanOptions

/-- The `comparators/HeatKernel` statements proved from the library. -/
@[default_target]
lean_lib «HeatKernelSolution» where
  roots := #[`comparators.HeatKernel.Solution]
  leanOptions := projectLeanOptions
