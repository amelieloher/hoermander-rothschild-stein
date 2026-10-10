-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import HeatKernel.Moser.MeanValueLinearTailTests
public import HeatKernel.Moser.NegativePowerCoefficients

/-! Uniform coercivity of reciprocal-power flux in half-power gradient coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace HeatKernel

/-- Half the reciprocal-power principal flux controls the gradient of the
negative half-power with a coefficient independent of its exponent. -/
theorem negative_half_power_gradient_le_half_principal {ell p s : ℝ}
    (hell : 0 < ell) (hp : 0 < p) (hs : 0 < s) (η a : ℝ) :
    2 * ell * (η * (p / 2 * s ^ (-p / 2 - 1)) * a) ^ 2 ≤
      p * ell * (p + 1) / 2 * s ^ (-p - 2) * (η * a) ^ 2 := by
  have hpow : (s ^ (-p / 2 - 1)) ^ 2 = s ^ (-p - 2) := by
    rw [← Real.rpow_natCast (s ^ (-p / 2 - 1)) 2, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hcoef : 2 * ell * (p / 2) ^ 2 ≤ p * ell * (p + 1) / 2 := by
    nlinarith [mul_pos hp hell]
  have h := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (Real.rpow_nonneg hs.le (-p - 2)) (sq_nonneg (η * a)))
  calc
    _ = (2 * ell * (p / 2) ^ 2) * (s ^ (-p - 2) * (η * a) ^ 2) := by
      rw [show (η * (p / 2 * s ^ (-p / 2 - 1)) * a) ^ 2 =
        (p / 2) ^ 2 * (s ^ (-p / 2 - 1)) ^ 2 * (η * a) ^ 2 by ring, hpow]
      ring
    _ ≤ _ := by convert h using 1; ring

end HeatKernel
