-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueEnergyNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! Reciprocal energy coefficients -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The reciprocal energy cost has a majorant independent of the initial
exponent. No quadratic loss in that exponent is needed. -/
theorem negative_power_energy_iteration_factor_le
    {A D χ p : ℝ} (hA : 1 ≤ A) (hD : 0 ≤ D) (hχ : 1 ≤ χ) (hp : 0 < p) :
    A ^ (1 / (p * χ)) * (2 * D) ^ (1 / p) ≤ (2 * A * D) ^ (1 / p) := by
  have hpow : 1 / (p * χ) ≤ 1 / p :=
    one_div_le_one_div_of_le hp (le_mul_of_one_le_right hp.le hχ)
  have hmajor := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hA hpow)
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * D) (1 / p))
  refine hmajor.trans_eq ?_
  rw [← Real.mul_rpow (by linarith : 0 ≤ A) (by positivity)]
  congr 1
  ring

/-- Extended norm arithmetic for the reciprocal energy coefficient. -/
theorem ennreal_negative_power_energy_iteration_factor_le
    {A D χ p : ℝ} (hA : 1 ≤ A) (hD : 0 ≤ D) (hχ : 1 ≤ χ) (hp : 0 < p) :
    ENNReal.ofReal A ^ (1 / (p * χ)) *
      (2 * ENNReal.ofReal D) ^ (1 / p) ≤ ENNReal.ofReal ((2 * A * D) ^ (1 / p)) := by
  have htwice : (2 : ENNReal) * ENNReal.ofReal D = ENNReal.ofReal (2 * D) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [htwice, ENNReal.ofReal_rpow_of_pos (by linarith : 0 < A),
    ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2 * D) (by positivity),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0 ≤ A) _)]
  exact ENNReal.ofReal_le_ofReal
    (negative_power_energy_iteration_factor_le hA hD hχ hp)

end HeatKernel
