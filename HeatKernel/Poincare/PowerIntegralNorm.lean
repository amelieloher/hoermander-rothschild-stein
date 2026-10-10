-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Normed.Group.Real

/-! Passing nonnegative power-integral estimates to finite-exponent seminorms. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- A power-integral bound yields the matching Lp seminorm bound, with no preliminary
integrability or finiteness requirement beyond almost-everywhere strong measurability. -/
theorem eLpNorm_le_of_abs_rpow_integral_le {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F] {μ : Measure E} {ν : Measure F}
    {f : E → ℝ} {g : F → ℝ} {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g ν)
    (hbound : (∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ) ≤
      ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal (|g x| ^ p) ∂ν) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) ν := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal hp.le]
  simp_rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  have hh := ENNReal.rpow_le_rpow hbound (one_div_nonneg.mpr hp.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp.le),
    ← ENNReal.ofReal_rpow_of_nonneg hC hp.le, ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one] at hh
  exact hh

end HeatKernel
