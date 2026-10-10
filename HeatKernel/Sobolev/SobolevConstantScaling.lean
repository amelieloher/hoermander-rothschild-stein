-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SobolevFromNash
import Mathlib.Tactic

/-! # Homogeneity of the weak and strong Sobolev constants -/

@[expose] public section
namespace HeatKernel.Sobolev

/-- Scaling the Nash coefficient by a power separates the same power in the weak constant. -/
theorem weakSobolevConstant_mul_rpow {C S d b : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) :
    weakSobolevConstant (C * S ^ d) b =
      weakSobolevConstant C b * S ^ (d / (1 - b)) := by
  unfold weakSobolevConstant
  rw [← mul_assoc, Real.mul_rpow
    (mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) _) hC)
    (Real.rpow_nonneg hS _), ← Real.rpow_mul hS]
  congr 2
  ring

/-- The subcritical interpolation constant has an explicit power homogeneity. -/
theorem subcriticalSobolevConstant_mul_rpow {C S d b p : ℝ}
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hp : 2 < p) (hpp : p < weakSobolevExponent b) :
    subcriticalSobolevConstant (C * S ^ d) b p = subcriticalSobolevConstant C b p *
      S ^ (d / (1 - b) * ((p - 2) / (weakSobolevExponent b - 2)) * (2 / p)) := by
  have hp₀ : 0 < p := by linarith
  have hA : 0 ≤ 1 / (1 - 2 / p) + 1 / (weakSobolevExponent b / p - 1) := by
    have hd₁ : 0 < 1 - 2 / p := sub_pos.mpr ((div_lt_one hp₀).mpr hp)
    have hd₂ : 0 < weakSobolevExponent b / p - 1 :=
      sub_pos.mpr ((one_lt_div hp₀).mpr hpp)
    positivity
  have hK : 0 ≤ weakSobolevConstant C b := by
    unfold weakSobolevConstant
    positivity
  unfold subcriticalSobolevConstant
  rw [weakSobolevConstant_mul_rpow hC hS,
    Real.mul_rpow hK (Real.rpow_nonneg hS _), ← Real.rpow_mul hS,
    ← mul_assoc, Real.mul_rpow (mul_nonneg hA (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hS _), ← Real.rpow_mul hS]

/-- Normalizing the Nash first moment gives the correct volume power in strong Sobolev. -/
theorem subcriticalSobolevConstant_sqrt_inv_volume {C V b p : ℝ}
    (hC : 0 ≤ C) (hV : 0 < V) (hb : 0 < b) (hb₁ : b < 1)
    (hp : 2 < p) (hpp : p < weakSobolevExponent b) :
    subcriticalSobolevConstant (C * (Real.sqrt V⁻¹) ^ b) b p =
      subcriticalSobolevConstant C b p * V ^ (2 / p - 1) := by
  have hd : 1 - b ≠ 0 := by linarith
  have hb₀ : b ≠ 0 := hb.ne'
  have hp₀ : p ≠ 0 := by linarith
  have heweak : weakSobolevExponent b - 2 = b / (1 - b) := by
    unfold weakSobolevExponent
    field_simp
    ring
  have he : b / (1 - b) * ((p - 2) / (weakSobolevExponent b - 2)) * (2 / p) =
      2 - 4 / p := by
    rw [heweak]
    field_simp
    ring
  rw [subcriticalSobolevConstant_mul_rpow hC (Real.sqrt_nonneg _) hp hpp, he]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (inv_nonneg.mpr hV.le),
    Real.inv_rpow hV.le, ← Real.rpow_neg hV.le]
  congr 1
  ring

end HeatKernel.Sobolev
