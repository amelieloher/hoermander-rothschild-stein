-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeightedMean
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Nonnegative integral minimization by weighted means -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A bounded weight supported in a set preserves integrability from that set. -/
theorem integrable_mul_of_bounded_support_weight {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : Set α} (hB : MeasurableSet B)
    {w f : α → ℝ} (hw : Measurable w) {C : ℝ} (hbound : ∀ x, ‖w x‖ ≤ C)
    (hzero : ∀ x, x ∉ B → w x = 0) (hf : IntegrableOn f B μ) :
    Integrable (fun x => w x * f x) μ := by
  have hfi : Integrable (B.indicator f) μ := (integrable_indicator_iff hB).mpr hf
  have H := hfi.bdd_mul hw.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  convert H using 1
  funext x
  by_cases hx : x ∈ B
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hzero x hx, mul_zero, zero_mul]

/-- The weighted mean minimizes nonnegative quadratic oscillation integrals. -/
theorem lintegral_weight_mul_sub_weightedMean_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w u : α → ℝ} (hw : Integrable w μ)
    (hu : AEStronglyMeasurable u μ) (hw₀ : ∀ x, 0 ≤ w x)
    (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ)
    (hmass : 0 < ∫ x, w x ∂μ) (c : ℝ) :
    (∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((u x - weightedMean μ w u) ^ 2) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((u x - c) ^ 2) ∂μ := by
  have hwn : 0 ≤ᵐ[μ] w := Filter.Eventually.of_forall hw₀
  have hwu := integrable_weight_mul_of_integrable_weight_mul_sq hw hu hwn hwu₂
  have hI (a : ℝ) : ENNReal.ofReal (∫ x, w x * (u x - a) ^ 2 ∂μ) =
      ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((u x - a) ^ 2) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_weight_mul_sub_sq hw hwu hwu₂ a)
      (Filter.Eventually.of_forall fun x => mul_nonneg (hw₀ x) (sq_nonneg _))]
    simp_rw [ENNReal.ofReal_mul (hw₀ _)]
  rw [← hI, ← hI]
  exact ENNReal.ofReal_le_ofReal
    (integral_weight_mul_sub_weightedMean_sq_le hw hwu hwu₂ hmass c)

end HeatKernel.Sobolev
