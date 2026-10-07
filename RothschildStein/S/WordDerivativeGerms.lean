-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.wordDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.S
variable {n q : ℕ}

/-- Every classical word depends only on the function's
local germ; no differentiability hypothesis is required for this
locality identity (BB pp. 77–79; zero-extension). -/
theorem wordDerivative_eventuallyEq
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (he : f =ᶠ[𝓝 x] g) :
    wordDerivative X I f =ᶠ[𝓝 x] wordDerivative X I g := by
  induction I with
  | nil => exact he
  | cons j I ih =>
    have hd := ih.fderiv (𝕜 := ℝ)
    filter_upwards [hd] with y hy
    change fderiv ℝ (wordDerivative X I f) y (X j y) =
      fderiv ℝ (wordDerivative X I g) y (X j y)
    rw [hy]

end RothschildStein.S
