-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.H2

/-- Cancel the positive dual-moment factor without assuming
a finite Lᵖ norm of the output (BB p. 326). -/
theorem dual_moment_root_le {I H p q : ℝ} (hI : 0 ≤ I) (hH : 0 ≤ H)
    (hp : 0 < p) (hpq : 1 / p + 1 / q = 1)
    (hbound : I ≤ H * I ^ (1 / q)) : I ^ (1 / p) ≤ H := by
  rcases eq_or_lt_of_le hI with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by positivity : 1 / p ≠ 0)]
    exact hH
  · have hpow : 0 < I ^ (1 / q) := Real.rpow_pos_of_pos hpos _
    apply (mul_le_mul_iff_of_pos_right hpow).mp
    rw [← Real.rpow_add hpos, hpq, Real.rpow_one]
    exact hbound

end RothschildStein.H2
