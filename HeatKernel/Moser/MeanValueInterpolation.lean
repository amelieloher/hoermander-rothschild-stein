-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # Spatial interpolation for parabolic mean-value estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Hölder interpolation raises a quadratic moment using a spatial Sobolev moment. -/
theorem lintegral_parabolic_power_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {ν : ℝ} (hν : 2 < ν) :
    (∫⁻ x, f x ^ (2 + 4 / ν) ∂μ) ≤
      (∫⁻ x, f x ^ (2 * ν / (ν - 2)) ∂μ) ^ ((ν - 2) / ν) *
        (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (2 / ν) := by
  have hn : ν ≠ 0 := by linarith
  have hd : ν - 2 ≠ 0 := by linarith
  have hp : 1 < ν / (ν - 2) := by
    apply (one_lt_div (by linarith : 0 < ν - 2)).mpr
    linarith
  have hc : (ν / (ν - 2)).HolderConjugate (ν / 2) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hp, ?_⟩
    field_simp
    ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    (hf.pow_const (2 : ℝ)) (hf.pow_const (4 / ν))
  have he : (4 / ν) * (ν / 2) = 2 := by field_simp; ring
  have he' : 1 / (ν / (ν - 2)) = (ν - 2) / ν := by field_simp
  have he'' : 1 / (ν / 2) = 2 / ν := by field_simp
  simpa only [Pi.mul_apply, ← ENNReal.rpow_add_of_nonneg (2 : ℝ) (4 / ν) (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 ≤ 4 / ν), ← ENNReal.rpow_mul, he, he', he'',
    show 2 * (ν / (ν - 2)) = 2 * ν / (ν - 2) by ring] using h

end HeatKernel
