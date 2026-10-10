-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeightedMean
import Mathlib.Tactic

/-!
# Quadratic estimates for normalized weighted averages

Jensen's quadratic inequality follows from the exact decomposition around the
weighted mean. This gives the pointwise oscillation inequality used to estimate
local averaging errors.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}

/-- Quadratic Jensen inequality for a nonnegative weight of mass one. -/
theorem sq_integral_weight_mul_le
    (hw : Integrable w μ) (hf : Integrable (fun x => w x * f x) μ)
    (hf₂ : Integrable (fun x => w x * f x ^ 2) μ)
    (hw₀ : 0 ≤ᵐ[μ] w) (hmass : (∫ x, w x ∂μ) = 1) :
    (∫ x, w x * f x ∂μ) ^ 2 ≤ ∫ x, w x * f x ^ 2 ∂μ := by
  have h := integral_weight_mul_sub_sq_eq hw hf hf₂ (by rw [hmass]; norm_num) 0
  have hnonneg : 0 ≤ ∫ x, w x * (f x - weightedMean μ w f) ^ 2 ∂μ :=
    integral_nonneg_of_ae (hw₀.mono (fun _ hx => mul_nonneg hx (sq_nonneg _)))
  simp only [sub_zero, hmass, one_mul] at h
  simpa only [weightedMean, hmass, div_one] using
    (show weightedMean μ w f ^ 2 ≤ ∫ x, w x * f x ^ 2 ∂μ by linarith)

/-- Squared distance to an average is controlled by a local oscillation and its average. -/
theorem sq_sub_integral_weight_mul_le
    (hw : Integrable w μ) (hf : Integrable (fun x => w x * f x) μ)
    (hf₂ : Integrable (fun x => w x * f x ^ 2) μ)
    (hw₀ : 0 ≤ᵐ[μ] w) (hmass : (∫ x, w x ∂μ) = 1) (z c : ℝ) :
    (z - ∫ x, w x * f x ∂μ) ^ 2 ≤
      2 * (z - c) ^ 2 + 2 * ∫ x, w x * (f x - c) ^ 2 ∂μ := by
  have hfc : Integrable (fun x => w x * (f x - c)) μ := by
    convert hf.sub (hw.mul_const c) using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hfc₂ := integrable_weight_mul_sub_sq hw hf hf₂ c
  have hmean : (∫ x, w x * (f x - c) ∂μ) = (∫ x, w x * f x ∂μ) - c := by
    have heq : (fun x => w x * (f x - c)) = (fun x => w x * f x - w x * c) := by
      funext x
      ring
    rw [heq, integral_sub hf (hw.mul_const c), integral_mul_const, hmass, one_mul]
  have h := sq_integral_weight_mul_le hw hfc hfc₂ hw₀ hmass
  rw [hmean] at h
  nlinarith [sq_nonneg ((z - c) + ((∫ x, w x * f x ∂μ) - c))]

end HeatKernel.Sobolev
