-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueCutoffRadii
import Mathlib.Tactic

/-! # Increasing radii for small-power absorption -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace HeatKernel

/-- Nested radii increasing from the inner radius toward the outer radius. -/
def increasingCutoffRadius (ρ R : ℝ) (j : ℕ) : ℝ :=
  ρ + R - nestedCutoffRadius ρ R j

@[simp] theorem increasingCutoffRadius_zero (ρ R : ℝ) : increasingCutoffRadius ρ R 0 = ρ := by
  simp only [increasingCutoffRadius, nestedCutoffRadius_zero]
  ring

/-- Increasing radii remain between the initial radius and the open outer radius. -/
theorem increasingCutoffRadius_mem_Ico {ρ R : ℝ} (hρR : ρ < R) (j : ℕ) :
    increasingCutoffRadius ρ R j ∈ Ico ρ R := by
  have hupper : nestedCutoffRadius ρ R j ≤ R := by
    induction j with
    | zero => simp only [nestedCutoffRadius_zero, le_refl]
    | succ j hj => exact (nestedCutoffRadius_succ_lt hρR j).le.trans hj
  have hlower := lt_nestedCutoffRadius hρR j
  dsimp only [increasingCutoffRadius]
  constructor <;> linarith

/-- Each successive increasing radius is strictly larger. -/
theorem increasingCutoffRadius_lt_succ {ρ R : ℝ} (hρR : ρ < R) (j : ℕ) :
    increasingCutoffRadius ρ R j < increasingCutoffRadius ρ R (j + 1) := by
  have h := nestedCutoffRadius_succ_lt hρR j
  dsimp only [increasingCutoffRadius]
  linarith

/-- Increasing and decreasing families have the same exact annular gaps. -/
theorem increasingCutoffRadius_succ_sub (ρ R : ℝ) (j : ℕ) :
    increasingCutoffRadius ρ R (j + 1) - increasingCutoffRadius ρ R j =
      (R - ρ) / 2 ^ (j + 1) := by
  calc
    _ = nestedCutoffRadius ρ R j - nestedCutoffRadius ρ R (j + 1) := by
      dsimp only [increasingCutoffRadius]
      ring
    _ = _ := nestedCutoffRadius_sub_succ ρ R j

/-- Every negative gap power has exact geometric growth along the increasing family. -/
theorem increasingCutoffRadius_gap_rpow_neg {ρ R : ℝ} (hρR : ρ < R) (κ : ℝ) (j : ℕ) :
    (increasingCutoffRadius ρ R (j + 1) - increasingCutoffRadius ρ R j) ^ (-κ) =
      (R - ρ) ^ (-κ) * ((2 : ℝ) ^ κ) ^ (j + 1) := by
  rw [increasingCutoffRadius_succ_sub,
    Real.div_rpow (sub_pos.mpr hρR).le (by positivity),
    Real.rpow_neg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) κ, div_inv_eq_mul]
  congr 1
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm ((j + 1 : ℕ) : ℝ) κ, Real.rpow_mul_natCast (by norm_num)]

end HeatKernel
