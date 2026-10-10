-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueLinearTailEnergy
import Mathlib.Tactic

/-! # Coercivity for the truncated half-power transform -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- Squaring the truncated half-power gives exactly the original value times the
positive-power energy test. -/
theorem linearTailPositivePower_half_sq {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) :
    linearTailPositivePower M (p / 2) s ^ 2 =
      s * linearTailPositivePower M (p - 1) s := by
  rw [linearTailPositivePower_eq_mul_min_rpow hM (by linarith) hs,
    linearTailPositivePower_eq_mul_min_rpow hM (by linarith) hs, mul_pow,
    ← Real.rpow_two ((min s M) ^ (p / 2 - 1)),
    ← Real.rpow_mul (le_min hs hM.le)]
  have he : (p / 2 - 1) * 2 = p - 1 - 1 := by ring
  rw [he]
  ring

/-- The normalized primitive controls the square of the half-power transform on
both sides of the truncation threshold. -/
theorem linearTailPositivePower_half_sq_le_primitive {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) :
    linearTailPositivePower M (p / 2) s ^ 2 ≤
      p * (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).primitive s := by
  have hpp : 0 < p := by linarith
  have hγ : 1 ≤ p - 1 := by linarith
  rw [linearTailPositivePower_half_sq hM hp hs]
  rcases le_total s M with hsM | hMs
  · rw [linearTailPositivePower_eq_rpow hs hsM,
      linearTailPowerWeakSolutionTest_primitive hM hγ hs hsM,
      sub_add_cancel, mul_div_cancel₀ _ hpp.ne']
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · subst s
      simp [Real.zero_rpow hpp.ne']
    · have he : s ^ p = s ^ (p - 1) * s := by
        simpa only [sub_add_cancel, Real.rpow_one] using Real.rpow_add hspos (p - 1) 1
      rw [he, mul_comm]
  · have hbound := linearTailPowerWeakSolutionTest_quadratic_le_primitive hM hγ hMs
    rw [sub_add_cancel] at hbound
    have hscaled := (div_le_iff₀ hpp).mp hbound
    rw [linearTailPositivePower_eq_linear hM hMs]
    nlinarith

/-- The truncated primitive is bounded by half the squared half-power on both
truncation regions, without an upper bound on the nonnegative argument. -/
theorem linearTailPowerWeakSolutionTest_primitive_le_half_sq {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) :
    (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p - 1 by linarith)).primitive s ≤
        linearTailPositivePower M (p / 2) s ^ 2 / 2 := by
  rcases le_total s M with hsM | hMs
  · rw [linearTailPowerWeakSolutionTest_primitive hM
      (show 1 ≤ p - 1 by linarith) hs hsM, sub_add_cancel,
      linearTailPositivePower_eq_rpow hs hsM,
      ← Real.rpow_two, ← Real.rpow_mul hs]
    have he : p / 2 * 2 = p := by ring
    rw [he]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hs _) (by norm_num) hp
  · rw [linearTailPowerWeakSolutionTest_primitive_above hM
      (show 1 ≤ p - 1 by linarith) hMs, sub_add_cancel,
      linearTailPositivePower_half_sq hM hp hs,
      linearTailPositivePower_eq_linear hM hMs]
    have he : M ^ p = M ^ (p - 1 - 1) * M ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hM]
      congr 1
      ring
    rw [he]
    have hdiv := div_le_div_of_nonneg_left
      (mul_nonneg (Real.rpow_nonneg hM.le (p - 1 - 1)) (sq_nonneg M))
      (by norm_num : (0 : ℝ) < 2) hp
    nlinarith only [hdiv]

/-- The square of the half-power chain factor is controlled by the positive-power
chain factor, including both corner levels and the linear upper tail. -/
theorem linearTailPositivePowerSlope_half_sq_le {M p s : ℝ}
    (hM : 0 < M) :
    (p - 1) * linearTailPositivePowerSlope M (p / 2) s ^ 2 ≤
      (p / 2) ^ 2 * linearTailPositivePowerSlope M (p - 1) s := by
  have he : (p / 2 - 1) * 2 = p - 1 - 1 := by ring
  have hsq (x : ℝ) (hx : 0 ≤ x) :
      (x ^ (p / 2 - 1)) ^ 2 = x ^ (p - 1 - 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx, he]
  by_cases hs : 0 < s
  · by_cases hsM : s < M
    · simp only [linearTailPositivePowerSlope, ite_eq_left hs, ite_eq_left hsM, mul_pow, hsq s hs.le]
      apply le_of_eq
      ring
    · simp only [linearTailPositivePowerSlope, ite_eq_left hs, ite_eq_right hsM, hsq M hM.le]
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (p - 2)])
        (Real.rpow_nonneg hM.le _)
  · simp [linearTailPositivePowerSlope, hs]

end HeatKernel
