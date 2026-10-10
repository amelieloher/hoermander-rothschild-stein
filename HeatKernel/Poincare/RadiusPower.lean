-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.Ring

/-! Extracting the radius power from weighted chain coefficients. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeatKernel

open scoped ENNReal

/-- The radius factor from the maximal Whitney radius combines with the chain
radius sum to produce exactly the exponent p. -/
theorem mul_radius_rpow_sub_one {J r p : ℝ} (hJ : 0 ≤ J) (hr : 0 < r) :
    (J * r) ^ (p - 1) * r = J ^ (p - 1) * r ^ p := by
  rw [Real.mul_rpow hJ hr.le, mul_assoc, ← Real.rpow_add_one hr.ne']
  congr 2
  ring

/-- The weighted radius coefficient is the pth power of a constant times the radius.
The constant is independent of the radius. -/
theorem ofReal_weighted_radius_eq_root_power {A J r p : ℝ}
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hr : 0 < r) (hp : 0 < p) :
    ENNReal.ofReal A * ENNReal.ofReal ((J * r) ^ (p - 1)) * ENNReal.ofReal r =
      ENNReal.ofReal (((A * J ^ (p - 1)) ^ (1 / p) * r) ^ p) := by
  have hroot : ((A * J ^ (p - 1)) ^ (1 / p)) ^ p = A * J ^ (p - 1) := by
    rw [← Real.rpow_mul (mul_nonneg hA (Real.rpow_nonneg hJ _)),
      one_div_mul_cancel hp.ne', Real.rpow_one]
  rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hA (Real.rpow_nonneg hJ _)) _) hr.le,
    hroot, ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg (mul_nonneg hJ hr.le) _))]
  congr 1
  rw [mul_assoc, mul_radius_rpow_sub_one hJ hr, ← mul_assoc]

end HeatKernel
