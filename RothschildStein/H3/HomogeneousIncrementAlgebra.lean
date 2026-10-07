-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The square-distance drift term reduces to the same
homogeneous increment scale under separation by a factor four. -/
theorem homogeneous_increment_drift_algebra {R r a M D : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hsep : 4 * r ≤ R)
    (hD : 0 ≤ D) :
    (2 * r) * M * (R / 2) ^ (a - 1) +
      (2 * r) ^ 2 * D * (R / 2) ^ (a - 2) ≤
        (2 : ℝ) ^ (2 - a) * (M + D) * r * R ^ (a - 1) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hp : (R / 2) ^ (a - 1) = (2 : ℝ) ^ (1 - a) * R ^ (a - 1) := by
    rw [Real.div_rpow hR.le htwo.le]
    have he : 1 - a = -(a - 1) := by ring
    rw [he, Real.rpow_neg htwo.le]
    ring
  have hq : (R / 2) ^ (a - 2) = (2 : ℝ) ^ (2 - a) * R ^ (a - 1) / R := by
    rw [Real.div_rpow hR.le htwo.le]
    have he : 2 - a = -(a - 2) := by ring
    have hex : a - 2 = (a - 1) - 1 := by ring
    rw [he, Real.rpow_neg htwo.le, hex, Real.rpow_sub_one hR.ne']
    ring
  have hc : (2 : ℝ) ^ (2 - a) = 2 * (2 : ℝ) ^ (1 - a) := by
    have he : 2 - a = (1 - a) + 1 := by ring
    rw [he, Real.rpow_add htwo, Real.rpow_one]
    ring
  have hrr : 4 * r ^ 2 / R ≤ r := by
    apply (div_le_iff₀ hR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsep hr]
  have hcoef : 0 ≤ (2 : ℝ) ^ (2 - a) * D * R ^ (a - 1) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg htwo.le _) hD)
      (Real.rpow_nonneg hR.le _)
  rw [hp, hq]
  calc
    _ = (2 : ℝ) ^ (2 - a) * M * r * R ^ (a - 1) +
        ((2 : ℝ) ^ (2 - a) * D * R ^ (a - 1)) * (4 * r ^ 2 / R) := by
      rw [hc]; ring
    _ ≤ (2 : ℝ) ^ (2 - a) * M * r * R ^ (a - 1) +
        ((2 : ℝ) ^ (2 - a) * D * R ^ (a - 1)) * r :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hrr hcoef)
    _ = _ := by ring

end RothschildStein.H3
