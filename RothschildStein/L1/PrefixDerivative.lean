-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.BracketProjection
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.L1

/-- A coordinate of the derivative is the derivative of the
scalar coordinate function, for the actual fderiv-based bracket formula. -/
theorem fderiv_coordinate_apply {N : ℕ} (Z : (Fin N → ℝ) → (Fin N → ℝ))
    {x : Fin N → ℝ} (hZ : DifferentiableAt ℝ Z x) (j : Fin N) (v : Fin N → ℝ) :
    fderiv ℝ (fun y => Z y j) x v = (fderiv ℝ Z x v) j := by
  change fderiv ℝ ((ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ) ∘ Z) x v = _
  rw [fderiv_comp x (ContinuousLinearMap.proj j).differentiableAt hZ,
    ContinuousLinearMap.fderiv]
  rfl

end RothschildStein.L1
