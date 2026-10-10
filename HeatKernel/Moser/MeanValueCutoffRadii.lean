-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Geometrically nested radii and exact annular gaps -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeatKernel

/-- Radii decreasing from an outer radius to an inner radius by halving the excess. -/
def nestedCutoffRadius (ρ R : ℝ) (j : ℕ) : ℝ := ρ + (R - ρ) / 2 ^ j

@[simp] theorem nestedCutoffRadius_zero (ρ R : ℝ) : nestedCutoffRadius ρ R 0 = R := by
  simp [nestedCutoffRadius]

/-- Each successive annular gap is exactly half of the preceding excess radius. -/
theorem nestedCutoffRadius_sub_succ (ρ R : ℝ) (j : ℕ) :
    nestedCutoffRadius ρ R j - nestedCutoffRadius ρ R (j + 1) =
      (R - ρ) / 2 ^ (j + 1) := by
  unfold nestedCutoffRadius
  rw [pow_succ]
  field_simp
  ring

/-- Strict outer and inner radii give strictly nested annuli at every index. -/
theorem nestedCutoffRadius_succ_lt {ρ R : ℝ} (hρR : ρ < R) (j : ℕ) :
    nestedCutoffRadius ρ R (j + 1) < nestedCutoffRadius ρ R j := by
  have h := div_pos (sub_pos.mpr hρR) (by positivity : (0 : ℝ) < 2 ^ (j + 1))
  rw [← nestedCutoffRadius_sub_succ] at h
  linarith

/-- All radii remain strictly above the limiting inner radius. -/
theorem lt_nestedCutoffRadius {ρ R : ℝ} (hρR : ρ < R) (j : ℕ) :
    ρ < nestedCutoffRadius ρ R j := by
  unfold nestedCutoffRadius
  have h := div_pos (sub_pos.mpr hρR) (by positivity : (0 : ℝ) < 2 ^ j)
  linarith

end HeatKernel
