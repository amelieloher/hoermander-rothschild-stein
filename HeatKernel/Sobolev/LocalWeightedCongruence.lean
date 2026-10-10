-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeightedMeanCongruence
import Mathlib.Tactic

/-! # Weighted quantities determined by local almost everywhere representatives -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A weighted mean depends only on the function on the support of its weight. -/
theorem weightedMean_congr_ae_restrict_support {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} (w : α → ℝ) (hw : Function.support w ⊆ S)
    {f g : α → ℝ} (he : f =ᵐ[μ.restrict S] g) :
    weightedMean μ w f = weightedMean μ w g := by
  unfold weightedMean
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict he] with x hx
  by_cases hs : x ∈ S
  · rw [hx hs]
  · have hz : w x = 0 := by
      by_contra hn
      exact hs (hw hn)
    simp [hz]

/-- Weighted variance is unchanged when representatives agree locally on the
support of the weight. -/
theorem lintegral_weighted_variance_congr_ae_restrict_support {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (w : α → ℝ) (hw : Function.support w ⊆ S)
    {f g : α → ℝ} (he : f =ᵐ[μ.restrict S] g) :
    (∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((f x - weightedMean μ w f) ^ 2) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((g x - weightedMean μ w g) ^ 2) ∂μ := by
  rw [weightedMean_congr_ae_restrict_support w hw he]
  apply lintegral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict he] with x hx
  by_cases hs : x ∈ S
  · rw [hx hs]
  · have hz : w x = 0 := by
      by_contra hn
      exact hs (hw hn)
    simp [hz]

/-- A weighted nonnegative integral depends only on its integrand on the weight support. -/
theorem lintegral_weight_mul_congr_ae_restrict_support {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (w : α → ℝ) (hw : Function.support w ⊆ S)
    {f g : α → ℝ≥0∞} (he : f =ᵐ[μ.restrict S] g) :
    (∫⁻ x, ENNReal.ofReal (w x) * f x ∂μ) = ∫⁻ x, ENNReal.ofReal (w x) * g x ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict he] with x hx
  by_cases hs : x ∈ S
  · rw [hx hs]
  · have hz : w x = 0 := by
      by_contra hn
      exact hs (hw hn)
    simp [hz]

end HeatKernel.Sobolev
