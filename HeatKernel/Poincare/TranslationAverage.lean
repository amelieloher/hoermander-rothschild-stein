-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Averaging translation bounds for nonnegative oscillation integrals. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace HeatKernel

/-- A probability-average oscillation bound and a uniform bound for translated differences
combine into an oscillation estimate. The averaging comparison, translation estimate, and
volume growth are separate explicit inputs. No measurable choice of curves is required. -/
theorem lintegral_oscillation_le_of_translation_estimate
    {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    {μ : Measure E} {ν : Measure Z} {B : Set E} {S : Set Z}
    {osc : E → ℝ≥0∞} {difference : Z → E → ℝ≥0∞} {A D : ℝ≥0∞}
    (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ⊤)
    (haverage : (∫⁻ y in B, osc y ∂μ) ≤
      (μ B)⁻¹ * ∫⁻ z in S, ∫⁻ y in B, difference z y ∂μ ∂ν)
    (htranslation : ∀ᵐ z ∂ν.restrict S, (∫⁻ y in B, difference z y ∂μ) ≤ A)
    (hvolume : ν S ≤ D * μ B) :
    (∫⁻ y in B, osc y ∂μ) ≤ D * A := by
  have hi : (∫⁻ z in S, ∫⁻ y in B, difference z y ∂μ ∂ν) ≤ A * ν S := by
    simpa only [lintegral_const, Measure.restrict_apply_univ] using
      (lintegral_mono_ae htranslation)
  calc
    (∫⁻ y in B, osc y ∂μ) ≤ (μ B)⁻¹ * (A * ν S) :=
      haverage.trans (mul_le_mul_right hi _)
    _ ≤ (μ B)⁻¹ * (A * (D * μ B)) :=
      mul_le_mul_right (mul_le_mul_right hvolume A) _
    _ = D * A := by
      calc
        (μ B)⁻¹ * (A * (D * μ B)) = ((μ B)⁻¹ * μ B) * (D * A) := by ac_rfl
        _ = D * A := by rw [ENNReal.inv_mul_cancel hB0 hBtop, one_mul]

end HeatKernel
