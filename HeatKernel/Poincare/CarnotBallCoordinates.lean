-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotBallVolume

/-! Coordinate transport of horizontal metric balls and their closures. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric RothschildStein

namespace HeatKernel.CarnotPoint

/-- The horizontal coordinate homeomorphism sends metric balls to literal horizontal
balls in the coordinate space. -/
theorem coordinateHomeomorph_image_ball {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) (r : ℝ) :
    coordinateHomeomorph G hq hqpos hspan '' ball x r =
      horizontalBall (G.horizontalFields hq) x r := by
  rw [ball_eq_horizontalBall G hq hqpos hspan x r]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- Coordinate transport preserves the closure of each horizontal metric ball. -/
theorem coordinateHomeomorph_image_closure_ball {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) (r : ℝ) :
    coordinateHomeomorph G hq hqpos hspan '' closure (ball x r) =
      closure (horizontalBall (G.horizontalFields hq) x r) := by
  rw [(coordinateHomeomorph G hq hqpos hspan).image_closure,
    coordinateHomeomorph_image_ball G hq hqpos hspan x r]

end HeatKernel.CarnotPoint
