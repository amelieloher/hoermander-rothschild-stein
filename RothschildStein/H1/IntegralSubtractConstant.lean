-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace RothschildStein.H1

/-- Subtracting a constant test value commutes with an
absolutely integrable coefficient and a bounded measurable test. -/
theorem integral_mul_sub_constant {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {a g : E → ℝ} (ha : Integrable a μ)
    (hg : AEStronglyMeasurable g μ) {B : ℝ} (hb : ∀ v, ‖g v‖ ≤ B) (c : ℝ) :
    (∫ v, a v * g v ∂μ) - c * (∫ v, a v ∂μ) = ∫ v, a v * (g v - c) ∂μ := by
  have hi : Integrable (fun v => a v * g v) μ := by
    apply (ha.norm.mul_const B).mono' (ha.aestronglyMeasurable.mul hg)
    apply Eventually.of_forall
    intro v
    change ‖a v * g v‖ ≤ ‖a v‖ * B
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg _)
  have he : (fun v => a v * (g v - c)) = fun v => a v * g v - c * a v := by
    funext v
    ring
  rw [he, integral_sub hi (ha.const_mul c), integral_const_mul]

end RothschildStein.H1
