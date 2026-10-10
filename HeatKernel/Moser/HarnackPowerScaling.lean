-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackLocalEstimates
import Mathlib.Tactic

/-! # Homogeneity of the power estimates in the Harnack comparison

Multiplication by a finite nonnegative constant preserves both the reverse
Hölder moment estimate and the reciprocal mean-value estimate. In particular,
the logarithmic shift can be chosen independently of the power estimates.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A positive power moment is homogeneous even when its integral is infinite. -/
theorem lintegral_rpow_norm_const_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) {p : ℝ} (hp : 0 < p)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    (∫⁻ y, (c * f y) ^ p ∂μ) ^ (1 / p) =
      c * (∫⁻ y, f y ^ p ∂μ) ^ (1 / p) := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- Scaling a function preserves a reverse Hölder moment estimate with the
same constant and exponents. -/
theorem reverseHolder_moment_bound_const_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) (S T : Set α) {p p₀ : ℝ}
    (hp : 0 < p) (hp₀ : 0 < p₀) {K c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : (∫⁻ y in S, f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
      K * (∫⁻ y in T, f y ^ p ∂μ) ^ (1 / p)) :
    (∫⁻ y in S, (c * f y) ^ p₀ ∂μ) ^ (1 / p₀) ≤
      K * (∫⁻ y in T, (c * f y) ^ p ∂μ) ^ (1 / p) := by
  rw [lintegral_rpow_norm_const_mul _ _ hp₀ hc,
    lintegral_rpow_norm_const_mul _ _ hp hc, mul_left_comm K c]
  exact mul_le_mul_right h c

/-- Scaling a function preserves its essential-supremum mean-value estimate. -/
theorem essSup_moment_bound_const_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) (S T : Set α) {p : ℝ}
    (hp : 0 < p) {K c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : essSup f (μ.restrict S) ≤ (K * ∫⁻ y in T, f y ^ p ∂μ) ^ (1 / p)) :
    essSup (fun y => c * f y) (μ.restrict S) ≤
      (K * ∫⁻ y in T, (c * f y) ^ p ∂μ) ^ (1 / p) := by
  rw [ENNReal.essSup_const_mul]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc),
    mul_left_comm K (c ^ p),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]
  exact mul_le_mul_right h c

end HeatKernel
