-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.WeightedMean
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Removing a constant from a normalized weighted mean -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- An integrable weighted quadratic deviation controls the first logarithmic
moment even when the function has first been centered by two constants. -/
theorem integrable_logarithmic_moment_of_variance
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}
    (hw : Integrable w μ) (hf : AEStronglyMeasurable f μ)
    (hwn : 0 ≤ᵐ[μ] w) (m c : ℝ)
    (hvar : Integrable (fun y => w y * (f y - c - m)^2) μ) :
    Integrable (fun y => w y * f y) μ := by
  have hcenter : AEStronglyMeasurable (fun y => f y - c - m) μ :=
    (hf.fun_sub aestronglyMeasurable_const).fun_sub aestronglyMeasurable_const
  have hfirst := Sobolev.integrable_weight_mul_of_integrable_weight_mul_sq hw hcenter hwn hvar
  apply (hfirst.add (hw.mul_const (m + c))).congr
  exact Filter.Eventually.of_forall fun y => by
    change w y * (f y - c - m) + w y * (m + c) = w y * f y
    ring

/-- Centering a logarithm by a constant and adding that constant back gives the
same normalized weighted mean, provided the first moment is integrable. -/
theorem normalized_logarithmic_mean_centering
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ}
    (hw : Integrable w μ) (hf : Integrable (fun y => w y * f y) μ)
    (hmass : (∫ y, w y ∂μ) ≠ 0) (c : ℝ) :
    (∫ y, w y ∂μ)⁻¹ * (∫ y, w y * (f y - c) ∂μ) + c =
      (∫ y, w y * f y ∂μ) / (∫ y, w y ∂μ) := by
  simp_rw [mul_sub]
  rw [integral_sub hf (hw.mul_const c), integral_mul_const]
  field_simp [hmass]
  ring

end HeatKernel
