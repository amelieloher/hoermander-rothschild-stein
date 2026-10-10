-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.AveragingKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Positive kernel bounds for signed real averages

The absolute value of a real average is controlled by the positive average of
the absolute value. Thus a column-mass estimate and a uniform kernel bound give
the same quadratic estimate for signed functions.
-/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A positive majorant controls the absolute value of a signed kernel integral. -/
theorem ofReal_abs_integral_kernel_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {r : α → α → ℝ} {k : α → α → ℝ≥0∞}
    (hmajorant : ∀ x y, ENNReal.ofReal |r x y| ≤ k x y) (f : α → ℝ) (x : α) :
    ENNReal.ofReal |∫ y, r x y * f y ∂μ| ≤
      ∫⁻ y, k x y * ENNReal.ofReal |f y| ∂μ := by
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal |r x y * f y| ∂μ := by
      simpa only [Real.enorm_eq_ofReal_abs] using
        (enorm_integral_le_lintegral_enorm (fun y => r x y * f y) (μ := μ))
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
      exact mul_le_mul' (hmajorant x y) le_rfl

/-- Positive column-mass and kernel bounds give the quadratic estimate for signed averages. -/
theorem lintegral_signed_averageKernel_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {r : α → α → ℝ} {k : α → α → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k))
    (hmajorant : ∀ x y, ENNReal.ofReal |r x y| ≤ k x y)
    (hcol : ∀ y, ∫⁻ x, k x y ∂μ ≤ 1) {c : ℝ≥0∞}
    (hkernel : ∀ x y, k x y ≤ c) {f : α → ℝ} (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal ((∫ y, r x y * f y ∂μ) ^ 2) ∂μ) ≤
      c * (∫⁻ y, ENNReal.ofReal |f y| ∂μ) ^ 2 := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, k x y * ENNReal.ofReal |f y| ∂μ) ^ 2 ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
      exact pow_le_pow_left' (ofReal_abs_integral_kernel_le hmajorant f x) 2
    _ ≤ _ := lintegral_averageKernel_sq_le hk (by fun_prop) hcol hkernel

end HeatKernel.Sobolev
