-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeightedMean
import Mathlib.Tactic.Linter

/-! # Independence of weighted means and variances from representatives -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel.Sobolev

/-- Weighted means are unchanged by an almost everywhere change of the function. -/
theorem weightedMean_congr_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w : α → ℝ) {f g : α → ℝ} (he : f =ᵐ[μ] g) :
    weightedMean μ w f = weightedMean μ w g := by
  unfold weightedMean
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

/-- The weighted squared distance to the weighted mean is independent of representatives. -/
theorem lintegral_weighted_variance_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (w : α → ℝ) {f g : α → ℝ} (he : f =ᵐ[μ] g) :
    (∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((f x - weightedMean μ w f) ^ 2) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (w x) * ENNReal.ofReal ((g x - weightedMean μ w g) ^ 2) ∂μ := by
  rw [weightedMean_congr_ae w he]
  apply lintegral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

/-- Squared distance to a set average is unchanged by an almost everywhere change
of the function on that set. -/
theorem lintegral_sub_setAverage_sq_congr_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (S : Set α) {f g : α → ℝ} (he : f =ᵐ[μ.restrict S] g) :
    (∫⁻ x in S, ENNReal.ofReal ((f x - (∫ y in S, f y ∂μ) / μ.real S) ^ 2) ∂μ) =
      ∫⁻ x in S, ENNReal.ofReal ((g x - (∫ y in S, g y ∂μ) / μ.real S) ^ 2) ∂μ := by
  rw [integral_congr_ae he]
  apply lintegral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

end HeatKernel.Sobolev
