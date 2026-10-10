-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueEnergyStep
public import HeatKernel.Moser.MeanValueBoundedPowerLimits
public import HeatKernel.Moser.TopExhaustionAlmostEverywhere
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! # A norm step from cutoff energy estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel

/-- Taking the next power root separates the Sobolev coefficient, energy coefficient
and input moment with their exact iteration exponents. -/
theorem parabolic_moment_root_le {p χ : ℝ} (hp : 0 < p) (hχ : 0 < χ)
    {I A D M : ℝ≥0∞} (hI : I ≤ A * (D * M) ^ χ) :
    I ^ (1 / (p * χ)) ≤ A ^ (1 / (p * χ)) * D ^ (1 / p) * M ^ (1 / p) := by
  have he : χ * (1 / (p * χ)) = 1 / p := by field_simp
  calc
    _ ≤ (A * (D * M) ^ χ) ^ (1 / (p * χ)) := ENNReal.rpow_le_rpow hI (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, he,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      ac_rfl

/-- A higher-moment estimate yields the actual extended Lp norm step on nested
measures. The higher-moment input is an explicit hypothesis. -/
theorem eLpNorm_step_le_of_parabolic_moment_bound
    {α : Type*} [MeasurableSpace α] (μinner μouter : Measure α) {f : α → ℝ}
    {p χ : ℝ} (hp : 0 < p) (hχ : 0 < χ)
    (hi : AEStronglyMeasurable f μinner) (ho : AEStronglyMeasurable f μouter)
    {A D : ℝ≥0∞}
    (hMoment : (∫⁻ x, ‖f x‖ₑ ^ (p * χ) ∂μinner) ≤
      A * (D * (∫⁻ x, ‖f x‖ₑ ^ p ∂μouter)) ^ χ) :
    eLpNorm f (ENNReal.ofReal (p * χ)) μinner ≤
      A ^ (1 / (p * χ)) * D ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) μouter := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr (mul_pos hp hχ)).ne'
      ENNReal.ofReal_ne_top hi,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top ho,
    ENNReal.toReal_ofReal (mul_pos hp hχ).le, ENNReal.toReal_ofReal hp.le]
  exact parabolic_moment_root_le hp hχ hMoment

end HeatKernel
