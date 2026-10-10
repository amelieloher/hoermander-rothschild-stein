-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyComparability

/-! Common averaging domains for neighboring Whitney balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- If two fivefold dilates meet and the first radius is at most twice the second,
the first original ball lies in the second twentyfold dilate. -/
theorem ball_subset_twenty_dilate_of_five_dilates_intersect {E : Type*} [PseudoMetricSpace E]
    {z w : E} {a b : ℝ} (ha : a ≤ 2 * b)
    (hmeet : (ball z (5 * a) ∩ ball w (5 * b)).Nonempty) :
    ball z a ⊆ ball w (20 * b) := by
  obtain ⟨t, htz, htw⟩ := hmeet
  have hz := mem_ball.mp htz
  have hw := mem_ball.mp htw
  have hb : 0 < b := by nlinarith [(show 0 ≤ dist t w from dist_nonneg)]
  intro y hy
  apply mem_ball.mpr
  have hyz := mem_ball.mp hy
  have ht := dist_triangle y z w
  have hzw := dist_triangle z t w
  rw [dist_comm z t] at hzw
  linarith

end HeatKernel
