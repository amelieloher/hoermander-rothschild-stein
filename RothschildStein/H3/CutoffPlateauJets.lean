-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.wordDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H3
variable {N q : ℕ}

/-- Classical words are local: equality near a point persists
after every ordered field derivative, with no regularity assumption on
the fields needed for this locality assertion. -/
theorem wordDerivative_eventuallyEq
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin q))
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (h : f =ᶠ[𝓝 x] g) :
    wordDerivative X I f =ᶠ[𝓝 x] wordDerivative X I g := by
  induction I with
  | nil => exact h
  | cons i I ih =>
    have hd := ih.fderiv (𝕜 := ℝ)
    filter_upwards [hd] with z hz
    exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (X i z)) hz

end RothschildStein.H3
