-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import HeatKernel.Moser.MeanValueLinearTailTests
public import HeatKernel.Moser.MeanValueHalfPowerEnergy
import Mathlib.Tactic

/-! # Coercivity of the truncated power flux for the half-power gradient -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- The half-power chain factor loses only a linear power coefficient, uniformly
above and below the truncation height and at its corner levels. -/
theorem linearTailPositivePowerSlope_half_sq_le_linear {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) :
    linearTailPositivePowerSlope M (p / 2) s ^ 2 ≤
      p / 2 * linearTailPositivePowerSlope M (p - 1) s := by
  have h := linearTailPositivePowerSlope_half_sq_le (p := p) (s := s) hM
  have hcoef : p / 2 ≤ p - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg (linearTailPositivePowerSlope M (p / 2) s))
  apply (mul_le_mul_iff_left₀ (show 0 < p / 2 by linarith)).mp
  nlinarith

end HeatKernel
