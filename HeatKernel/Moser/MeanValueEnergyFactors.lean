-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueCutoffRadii
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! # Geometric coefficients for the positive-power norm iteration -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- The Sobolev factor and the quadratic power-cutoff cost have one geometric
majorant. Its constants are independent of the iteration index and the gap. -/
theorem parabolic_energy_iteration_factor_le
    {A K χ δ : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hχ : 1 < χ)
    (hδ : 0 < δ) (j : ℕ) :
    A ^ (1 / ((2 * χ ^ j) * χ)) *
      (2 * (K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2)) ^ (1 / (2 * χ ^ j)) ≤
        (8 * A * K * (4 * χ ^ 2) ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j)) := by
  have hp : 0 < 2 * χ ^ j := by positivity
  have hpow : 1 / ((2 * χ ^ j) * χ) ≤ 1 / (2 * χ ^ j) := by
    apply one_div_le_one_div_of_le hp
    exact le_mul_of_one_le_right hp.le hχ.le
  have hmajor := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hA hpow)
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * (K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2)) (1 / (2 * χ ^ j)))
  refine hmajor.trans_eq ?_
  rw [← Real.mul_rpow (by linarith : 0 ≤ A) (by positivity)]
  congr 1
  have hpowers : (χ ^ j) ^ 2 * 4 ^ j = (4 * χ ^ 2) ^ j := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
    ring
  calc
    A * (2 * (K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2)) =
        8 * A * K * ((χ ^ j) ^ 2 * 4 ^ j) / δ ^ 2 := by ring
    _ = _ := by rw [hpowers]

/-- The same majorant in the extended norm arithmetic used by Moser iteration. -/
theorem ennreal_parabolic_energy_iteration_factor_le
    {A K χ δ : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hχ : 1 < χ)
    (hδ : 0 < δ) (j : ℕ) :
    ENNReal.ofReal A ^ (1 / ((2 * χ ^ j) * χ)) *
      (2 * ENNReal.ofReal (K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2)) ^ (1 / (2 * χ ^ j)) ≤
        ENNReal.ofReal ((8 * A * K * (4 * χ ^ 2) ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j))) := by
  have hA0 : 0 ≤ A := by linarith
  have hcost : 0 ≤ K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2 := by positivity
  have htwice : (2 : ENNReal) * ENNReal.ofReal (K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2) =
      ENNReal.ofReal (2 * (K * (2 * χ ^ j) ^ 2 * 4 ^ j / δ ^ 2)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [htwice, ENNReal.ofReal_rpow_of_pos (by linarith : 0 < A),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by norm_num) hcost) (by positivity),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hA0 _)]
  exact ENNReal.ofReal_le_ofReal (parabolic_energy_iteration_factor_le hA hK hχ hδ j)

end HeatKernel
