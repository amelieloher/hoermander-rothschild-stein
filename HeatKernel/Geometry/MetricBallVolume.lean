-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CoordinateBall

/-! Exact volume formulas for horizontal metric balls, including radius zero. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

variable {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
  (hspan : bracketSpansOn univ (G.horizontalFields hq))
  (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)

include hw

/-- The metric unit ball has positive finite coordinate volume. -/
theorem volume_unitBall_pos_finite :
    0 < (CarnotPoint.volume G hq hqpos hspan)
      (Metric.ball (0 : Fin N → ℝ) 1) ∧
    (CarnotPoint.volume G hq hqpos hspan)
      (Metric.ball (0 : Fin N → ℝ) 1) < ⊤ := by
  change 0 < (MeasureTheory.volume : Measure (Fin N → ℝ))
      (coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)) ∧
    (MeasureTheory.volume : Measure (Fin N → ℝ))
      (coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ)) < ⊤
  erw [coordinateBall_eq_horizontalBall]
  exact ⟨volume_horizontalBall_pos G hq hqpos hspan 0 (by norm_num),
    volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by norm_num)⟩

/-- Every nonnegative-radius metric ball has the exact homogeneous volume. -/
theorem volume_ball_of_nonneg (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 ≤ r) :
    (CarnotPoint.volume G hq hqpos hspan) (Metric.ball x r) = ENNReal.ofReal (r ^ G.homogeneousDimension) *
      (CarnotPoint.volume G hq hqpos hspan) (Metric.ball (0 : Fin N → ℝ) 1) := by
  rcases hr.eq_or_lt with hzero | hpos
  · subst r
    have hd : G.homogeneousDimension ≠ 0 := by
      exact ne_of_gt (G2.homogeneousDimension_pos G)
    simp [hd]
  · change (MeasureTheory.volume : Measure (Fin N → ℝ))
        (coordinateBall G hq hqpos hspan x r : Set (Fin N → ℝ)) =
      ENNReal.ofReal (r ^ G.homogeneousDimension) *
        (MeasureTheory.volume : Measure (Fin N → ℝ))
          (coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1 : Set (Fin N → ℝ))
    erw [coordinateBall_eq_horizontalBall, coordinateBall_eq_horizontalBall]
    exact volume_horizontalBall G hq hw x hpos

end HeatKernel.CarnotPoint
