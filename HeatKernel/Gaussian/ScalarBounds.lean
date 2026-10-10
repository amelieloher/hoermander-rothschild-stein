-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Scalar estimates for Gaussian bounds

Completing the square optimizes weighted exponential estimates. Exact homogeneous
ball volumes identify the symmetric volume factor with a single volume.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HeatKernel.Gaussian

/-- The linear loss in a two-endpoint estimate can be absorbed into the Gaussian. -/
theorem exp_quadratic_linear_le (a : ℝ) :
    Real.exp (-a ^ 2 / 12 + a / 6) ≤
      Real.exp (1 / 6) * Real.exp (-a ^ 2 / 24) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (a - 2)]

end HeatKernel.Gaussian
