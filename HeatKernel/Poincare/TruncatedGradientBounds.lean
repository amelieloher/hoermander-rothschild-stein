-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.FiniteGradientLength
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace HeatKernel

/-- Each component is bounded by the Euclidean length of a finite vector. -/
theorem abs_le_finite_gradient_length {q : ℕ} (g : Fin q → ℝ) (i : Fin q) :
    |g i| ≤ Real.sqrt (∑ j, g j ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i)

/-- Restricting all components to the same predicate does not increase their
Euclidean length. -/
theorem finite_gradient_length_ite_le {q : ℕ} (g : Fin q → ℝ) (P : Prop) [Decidable P] :
    Real.sqrt (∑ j, (if P then g j else 0) ^ 2) ≤ Real.sqrt (∑ j, g j ^ 2) := by
  by_cases h : P
  · simp only [ite_eq_left h, le_refl]
  · simp only [ite_eq_right h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

end HeatKernel
