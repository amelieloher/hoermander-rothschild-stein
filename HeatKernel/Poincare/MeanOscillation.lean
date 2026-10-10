-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Jensen estimates for the oscillation from an integral mean, including exponent one. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set

namespace HeatKernel

/-- The absolute value of an integral average is bounded by the average absolute value. -/
theorem abs_average_le_average_abs {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) : |⨍ x, f x ∂μ| ≤ ⨍ x, |f x| ∂μ := by
  simpa only [average_eq', Real.norm_eq_abs] using
    (norm_integral_le_integral_norm f (μ := (μ univ)⁻¹ • μ))

/-- Jensen's inequality for absolute powers of an average, valid also at exponent one. -/
theorem abs_average_rpow_le_average_abs_rpow {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {f : E → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Integrable f μ)
    (hfp : Integrable (fun x => |f x| ^ p) μ) :
    |⨍ x, f x ∂μ| ^ p ≤ ⨍ x, |f x| ^ p ∂μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  apply (Real.rpow_le_rpow (abs_nonneg _) (abs_average_le_average_abs μ f) hp0).trans
  exact (convexOn_rpow hp).map_average_le (Real.continuous_rpow_const hp0).continuousOn
    isClosed_Ici (Filter.Eventually.of_forall fun x => abs_nonneg (f x)) hf.abs hfp

/-- The pointwise oscillation from the mean is bounded by the averaged pairwise
oscillation, without a change in the exponent or a limiting argument at exponent one. -/
theorem abs_sub_average_rpow_le_average_abs_sub_rpow {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {f : E → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Integrable f μ) (c : ℝ)
    (hfp : Integrable (fun x => |c - f x| ^ p) μ) :
    |c - ⨍ x, f x ∂μ| ^ p ≤ ⨍ x, |c - f x| ^ p ∂μ := by
  have hh := abs_average_rpow_le_average_abs_rpow hp ((integrable_const c).sub hf) hfp
  rw [average_sub (integrable_const c) hf, average_const] at hh
  simpa only [Pi.sub_apply] using hh

end HeatKernel
