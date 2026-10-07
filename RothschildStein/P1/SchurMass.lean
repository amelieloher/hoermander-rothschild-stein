-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Tonelli and the column absolute-mass bound control the total
absolute output mass. The constant is independent of the input. -/
theorem kernel_column_lintegral_bound (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (B : ℝ≥0∞)
    (hcolumn : ∀ y, (∫⁻ x, K x y ∂μ) ≤ B)
    (f : β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, K x y * f y ∂ν ∂μ) ≤ B * ∫⁻ y, f y ∂ν := by
  rw [lintegral_lintegral_swap (hK.mul (hf.comp measurable_snd)).aemeasurable]
  calc
    _ = ∫⁻ y, (∫⁻ x, K x y ∂μ) * f y ∂ν := by
      apply lintegral_congr
      intro y
      exact lintegral_mul_const (f y) hK.of_uncurry_right
    _ ≤ ∫⁻ y, B * f y ∂ν :=
      lintegral_mono (fun y => mul_le_mul_left (hcolumn y) (f y))
    _ = _ := lintegral_const_mul B hf

end RothschildStein.P1
