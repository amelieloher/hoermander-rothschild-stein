-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WeakLocal

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Positivity of the explicit weak-type coefficient
(BB pp. 320, 326). -/
theorem nonnegativeWeakConstant_nonneg (D : LocDoubling X) {β S cT m : ℝ}
    (hβ : 0 < β) (hS : 0 ≤ S) : 0 ≤ nonnegativeWeakConstant D β S cT m := by
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  have hN : 0 ≤ D.C_D ^ 7 + D.C_D ^ 5 := add_nonneg (pow_nonneg hCD _) (pow_nonneg hCD _)
  have hG : 0 ≤ goodAverageConstant D m := (pow_nonneg hCD 6).trans (le_max_left _ _)
  unfold nonnegativeWeakConstant
  exact add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg cT)) (mul_nonneg hN hG))
    (mul_nonneg (sq_nonneg D.C_D) hN))
    (mul_nonneg (by norm_num) (mul_nonneg
      (mul_nonneg hS (hedbergVolumeIntegralConstant_pos (by linarith [D.one_lt_C_D]) hβ).le)
      (Real.rpow_nonneg (by norm_num) _)))

end RothschildStein.H2
