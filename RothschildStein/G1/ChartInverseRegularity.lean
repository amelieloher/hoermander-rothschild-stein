-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.QuantitativeCharts
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear perturbation within 1/(2P) of A is invertible, with
inverse norm at most 2P (BB Thm 1.43, pp. 24–25). -/
theorem chart_linearPerturbation_inverse (A : E ≃L[ℝ] E) (D : E →L[ℝ] E)
    {P : ℝ} (hP : 0 < P) (hA : ‖(A.symm : E →L[ℝ] E)‖ ≤ P)
    (hbound : ‖D - (A : E →L[ℝ] E)‖ ≤ 1 / (2 * P)) :
    ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = D ∧ ‖(L.symm : E →L[ℝ] E)‖ ≤ 2 * P := by
  have hinj : Function.Injective D := by
    exact injOn_univ.mp (chart_injOn_of_derivative_bound A hP hA convex_univ
      (fun x _ => D.hasFDerivAt) (fun _ _ => hbound))
  let L : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv
  have hL : (L : E →L[ℝ] E) = D := by ext v; rfl
  refine ⟨L, hL, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h := chart_inverse_parameter_bound A hP hA convex_univ
    (fun x _ => D.hasFDerivAt) (fun _ _ => hbound)
    (x := L.symm v) (y := 0) (mem_univ _) (mem_univ _)
  have hv : D (L.symm v) = v := by rw [← hL]; exact L.apply_symm_apply v
  change ‖L.symm v‖ ≤ 2 * P * ‖v‖
  simpa only [sub_zero, map_zero, hv] using h

end RothschildStein.G1
