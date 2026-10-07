-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Calculus.VectorField
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- Actual brackets distribute over a finite smooth field sum. The
identity retains the derivative of every summand field. -/
theorem lieBracket_finset_sum_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (T : Finset ι) (V : E → E) (W : ι → E → E) (x : E)
    (hW : ∀ i ∈ T, DifferentiableAt ℝ (W i) x) :
    VectorField.lieBracket ℝ V (fun y => ∑ i ∈ T, W i y) x =
      ∑ i ∈ T, VectorField.lieBracket ℝ V (W i) x := by
  simp only [VectorField.lieBracket]
  rw [fderiv_fun_sum hW]
  simp only [sum_apply,map_sum,Finset.sum_sub_distrib]
end RothschildStein.L1
