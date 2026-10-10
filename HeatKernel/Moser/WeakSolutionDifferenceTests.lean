-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionTimeAverageTests

/-!
# Translation of time difference tests

Translation invariance of Lebesgue measure moves backward differences of a
scalar test onto forward differences of a Banach-valued curve.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translating the scalar test is equivalent to translating the curve in the
opposite direction, even when the Bochner integral is defined to be zero. -/
theorem integral_shifted_time_test (ψ : ℝ → ℝ) (D : ℝ → E) (h : ℝ) :
    (∫ t, ψ (t - h) • D t) = ∫ t, ψ t • D (t + h) := by
  have ht := integral_add_right_eq_self (μ := volume)
    (fun t => ψ (t - h) • D t) h
  simpa only [add_sub_cancel_right] using ht.symm

/-- A backward difference of an integrable test pairs with the negative forward
 difference of the curve. -/
theorem integral_backward_difference_test {ψ : ℝ → ℝ} {D : ℝ → E} (h : ℝ)
    (hzero : Integrable (fun t => ψ t • D t))
    (hshift : Integrable (fun t => ψ t • D (t + h))) :
    (∫ t, (ψ t - ψ (t - h)) • D t) =
      -(∫ t, ψ t • (D (t + h) - D t)) := by
  have hs : Integrable (fun t => ψ (t - h) • D t) := by
    simpa only [sub_add_cancel] using hshift.comp_sub_right h
  simp_rw [sub_smul, smul_sub]
  rw [integral_sub hzero hs, integral_sub hshift hzero,
    integral_shifted_time_test]
  exact (neg_sub _ _).symm

/-- Difference quotients satisfy the same adjoint identity as unscaled differences. -/
theorem integral_backward_difference_quotient_test {ψ : ℝ → ℝ} {D : ℝ → E} (h : ℝ)
    (hzero : Integrable (fun t => ψ t • D t))
    (hshift : Integrable (fun t => ψ t • D (t + h))) :
    (∫ t, (h⁻¹ • (ψ t - ψ (t - h))) • D t) =
      -(∫ t, ψ t • (h⁻¹ • (D (t + h) - D t))) := by
  simp only [smul_eq_mul, mul_smul]
  simp_rw [smul_comm (ψ _) h⁻¹]
  rw [integral_smul, integral_smul,
    integral_backward_difference_test h hzero hshift, smul_neg]

end HeatKernel
