-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeightedMean
import Mathlib.Tactic

/-! # Comparing normalized means for nested nonnegative weights

For indicators of nested balls, the coefficient is one plus the ratio of their
volumes. The proof uses the exact quadratic mean decomposition twice.
-/

@[expose] public section
open MeasureTheory
namespace HeatKernel.Sobolev

/-- Replacing the mean for a larger weight by the mean for a smaller weight costs at most
one plus their mass ratio. -/
theorem integral_weight_mul_sub_nested_weightedMean_sq_le {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {u v w : α → ℝ}
    (hv : Integrable v μ) (hw : Integrable w μ)
    (hvu : Integrable (fun x => v x * u x) μ)
    (hwu : Integrable (fun x => w x * u x) μ)
    (hvu₂ : Integrable (fun x => v x * u x ^ 2) μ)
    (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ)
    (hv₀ : 0 ≤ᵐ[μ] v) (hvw : v ≤ᵐ[μ] w)
    (hMv : 0 < ∫ x, v x ∂μ) :
    (∫ x, w x * (u x - weightedMean μ v u) ^ 2 ∂μ) ≤
      (1 + (∫ x, w x ∂μ) / (∫ x, v x ∂μ)) *
        ∫ x, w x * (u x - weightedMean μ w u) ^ 2 ∂μ := by
  have hMw : 0 < ∫ x, w x ∂μ := hMv.trans_le (integral_mono_ae hv hw hvw)
  have hsmall := integral_weight_mul_sub_sq_eq hv hvu hvu₂ hMv.ne'
    (weightedMean μ w u)
  have hnonneg : 0 ≤ ∫ x, v x * (u x - weightedMean μ v u) ^ 2 ∂μ :=
    integral_nonneg_of_ae (hv₀.mono fun x hx => mul_nonneg hx (sq_nonneg _))
  have hmono : (∫ x, v x * (u x - weightedMean μ w u) ^ 2 ∂μ) ≤
      ∫ x, w x * (u x - weightedMean μ w u) ^ 2 ∂μ := by
    apply integral_mono_ae
      (integrable_weight_mul_sub_sq hv hvu hvu₂ _)
      (integrable_weight_mul_sub_sq hw hwu hwu₂ _)
    exact hvw.mono (fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg _))
  have hstep : (∫ x, v x ∂μ) * (weightedMean μ v u - weightedMean μ w u) ^ 2 ≤
      ∫ x, w x * (u x - weightedMean μ w u) ^ 2 ∂μ := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hstep (div_nonneg hMw.le hMv.le)
  have he : ((∫ x, w x ∂μ) / (∫ x, v x ∂μ)) *
      ((∫ x, v x ∂μ) * (weightedMean μ v u - weightedMean μ w u) ^ 2) =
      (∫ x, w x ∂μ) * (weightedMean μ w u - weightedMean μ v u) ^ 2 := by
    field_simp [hMv.ne']
    ring
  rw [he] at hscaled
  rw [integral_weight_mul_sub_sq_eq hw hwu hwu₂ hMw.ne']
  nlinarith

end HeatKernel.Sobolev
