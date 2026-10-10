-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNormalizedScaling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Common reference normalization of finite reverse-Hölder norm steps. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A common finite reference mass changes only the exponent-independent
energy constant of a norm step. Both the inner and outer norms use that same
mass, without assuming that the inner measure is a probability measure. -/
theorem eLpNorm_small_power_step_le_after_reference_normalization
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (f : α → ℝ)
    {m : ℝ≥0∞} {p χ D : ℝ} (hm : m ≠ 0) (hmtop : m ≠ ⊤)
    (hp : 0 < p) (hχ : 1 ≤ χ) (hD : 0 ≤ D)
    (h : eLpNorm f (ENNReal.ofReal (p * χ)) μ ≤
      ENNReal.ofReal (D ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) ν) :
    eLpNorm f (ENNReal.ofReal (p * χ)) (m⁻¹ • μ) ≤
      ENNReal.ofReal ((D * max 1 m.toReal * max 1 m.toReal⁻¹) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) (m⁻¹ • ν) := by
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hm hmtop
  have hχpos : 0 < χ := zero_lt_one.trans_le hχ
  have hpc : 0 < p * χ := mul_pos hp hχpos
  have hexp : 1 / (p * χ) ≤ 1 / p :=
    one_div_le_one_div_of_le hp (le_mul_of_one_le_right hp.le hχ)
  have hleft : eLpNorm f (ENNReal.ofReal (p * χ)) (m⁻¹ • μ) =
      ENNReal.ofReal ((m.toReal⁻¹) ^ (1 / (p * χ))) *
        eLpNorm f (ENNReal.ofReal (p * χ)) μ := by
    rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (ENNReal.ofReal_pos.mpr hpc).ne'
      ENNReal.ofReal_ne_top]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hpc.le, smul_eq_mul]
    rw [← ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hmpos),
      ENNReal.ofReal_inv_of_pos hmpos, ENNReal.ofReal_toReal hmtop]
  have hsmall : (m.toReal⁻¹) ^ (1 / (p * χ)) ≤
      (max 1 m.toReal⁻¹) ^ (1 / p) :=
    (Real.rpow_le_rpow (inv_nonneg.mpr hmpos.le) (le_max_right _ _) (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hexp)
  have hlarge : m.toReal ^ (1 / p) ≤ (max 1 m.toReal) ^ (1 / p) :=
    Real.rpow_le_rpow hmpos.le (le_max_right _ _) (by positivity)
  have hfactor : (m.toReal⁻¹) ^ (1 / (p * χ)) * D ^ (1 / p) * m.toReal ^ (1 / p) ≤
      (D * max 1 m.toReal * max 1 m.toReal⁻¹) ^ (1 / p) := by
    calc
      _ ≤ (max 1 m.toReal⁻¹) ^ (1 / p) * D ^ (1 / p) *
          (max 1 m.toReal) ^ (1 / p) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hD _))
          hlarge (Real.rpow_nonneg hmpos.le _) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (mul_nonneg hD (by positivity)) (by positivity),
          Real.mul_rpow hD (by positivity)]
        ring
  rw [hleft]
  calc
    _ ≤ ENNReal.ofReal ((m.toReal⁻¹) ^ (1 / (p * χ))) *
        (ENNReal.ofReal (D ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) ν) :=
      mul_le_mul' le_rfl h
    _ = ENNReal.ofReal ((m.toReal⁻¹) ^ (1 / (p * χ)) * D ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) ν := by
      rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ = ENNReal.ofReal (((m.toReal⁻¹) ^ (1 / (p * χ)) * D ^ (1 / p)) *
        m.toReal ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) (m⁻¹ • ν) :=
      mul_eLpNorm_eq_normalized_eLpNorm ν f hp (by positivity) hm hmtop
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) le_rfl

end HeatKernel
