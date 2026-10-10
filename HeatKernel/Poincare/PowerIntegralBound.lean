-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Normed.Group.Real

/-! Recovering power-integral estimates from finite-exponent oscillation bounds. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Raising a finite-exponent seminorm bound to its exponent gives a power-integral
bound, including when the integral has not previously been shown finite. -/
theorem lintegral_abs_rpow_le_of_eLpNorm_le {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {f : E → ℝ} {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f μ)
    (hbound : eLpNorm f (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal C * μ Set.univ ^ (1 / p)) :
    (∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ) ≤ ENNReal.ofReal (C ^ p) * μ Set.univ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le] at hbound
  simp_rw [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le] at hbound
  have hh := ENNReal.rpow_le_rpow hbound hp.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC hp.le] at hh
  exact hh

end HeatKernel
