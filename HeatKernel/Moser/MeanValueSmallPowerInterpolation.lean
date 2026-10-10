-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # Interpolation below the quadratic mean-value exponent -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A bounded function's quadratic moment is controlled by its small-power moment. -/
theorem lintegral_sq_le_small_power_of_ae_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {S : ℝ≥0∞} (hS : ∀ᵐ x ∂μ, f x ≤ S)
    {p : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    (∫⁻ x, f x ^ (2 : ℝ) ∂μ) ≤ S ^ (2 - p) * (∫⁻ x, f x ^ p ∂μ) := by
  calc
    _ = ∫⁻ x, f x ^ (2 - p) * f x ^ p ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hp2.le) hp.le,
        sub_add_cancel]
    _ ≤ ∫⁻ x, S ^ (2 - p) * f x ^ p ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hS] with x hx
      exact mul_le_mul' (ENNReal.rpow_le_rpow hx (sub_nonneg.mpr hp2.le)) le_rfl
    _ = _ := lintegral_const_mul'' _ (hf.pow_const p)

/-- Interpolating an essential bound with a small-power norm controls the quadratic norm. -/
theorem eLpNorm_two_le_small_power_of_ae_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {S : ℝ≥0∞}
    (hS : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ S) {p : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    eLpNorm f 2 μ ≤ S ^ (1 - p / 2) * eLpNorm f (ENNReal.ofReal p) μ ^ (p / 2) := by
  have hLp : eLpNorm f (ENNReal.ofReal p) μ ^ (p / 2) =
      (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
    congr 1
    field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf, ENNReal.toReal_ofNat, hLp]
  calc
    _ ≤ (S ^ (2 - p) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (lintegral_sq_le_small_power_of_ae_bound μ hf.enorm hS hp hp2)
        (by norm_num)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.rpow_mul]
      congr 2
      ring

end HeatKernel
