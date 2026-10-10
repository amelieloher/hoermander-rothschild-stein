-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Real weighted estimates from nonnegative integral inequalities -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel.Sobolev

/-- Separate integrability of weighted variance and energy converts their
nonnegative integral inequality to a real integral inequality. -/
theorem integral_weighted_variance_le_of_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w f e : α → ℝ} {c C : ℝ}
    (hw : ∀ x, 0 ≤ w x) (he : ∀ x, 0 ≤ e x) (hC : 0 ≤ C)
    (hi : Integrable (fun x => w x * (f x - c) ^ 2) μ)
    (hj : Integrable (fun x => w x * e x) μ)
    (hbound : (∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((f x - c) ^ 2) ∂μ) ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal (e x) ∂μ) :
    (∫ x, w x * (f x - c) ^ 2 ∂μ) ≤ C * ∫ x, w x * e x ∂μ := by
  have hleft := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => mul_nonneg (hw x) (sq_nonneg _)))
  have hright := ofReal_integral_eq_lintegral_ofReal hj
    (Filter.Eventually.of_forall (fun x => mul_nonneg (hw x) (he x)))
  simp only [ENNReal.ofReal_mul (hw _)] at hleft hright
  rw [← hleft, ← hright, ← ENNReal.ofReal_mul hC] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (integral_nonneg (fun x => mul_nonneg (hw x) (he x))))).mp hbound

end HeatKernel.Sobolev
