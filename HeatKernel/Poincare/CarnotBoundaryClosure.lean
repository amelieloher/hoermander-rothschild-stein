-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotBallCoordinates
public import HeatKernel.Poincare.WhitneyInterior

/-! Coordinate interior containment of strict boundary-distance dilates. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric RothschildStein

namespace HeatKernel.CarnotPoint

/-- In coordinates, every strict boundary-distance dilate has closure contained in the
original horizontal ball. Complement nonemptiness is an explicit geometric input. -/
theorem closure_horizontalBall_boundaryRadius_subset {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    {x z : CarnotPoint G hq hqpos hspan} {r c κ : ℝ}
    (hcompl : (ball x r)ᶜ.Nonempty) (hz : z ∈ ball x r) (hκ : 0 < κ) (hc : c < κ) :
    closure (horizontalBall (G.horizontalFields hq) z (c * (infDist z (ball x r)ᶜ / κ))) ⊆
      horizontalBall (G.horizontalFields hq) x r := by
  have hs : closure (ball z (c * (infDist z (ball x r)ᶜ / κ))) ⊆ ball x r :=
    closure_ball_subset_closedBall.trans
      (closedBall_boundaryRadius_subset isOpen_ball hcompl hz hκ hc)
  have hi : coordinateHomeomorph G hq hqpos hspan ''
      closure (ball z (c * (infDist z (ball x r)ᶜ / κ))) ⊆
      coordinateHomeomorph G hq hqpos hspan '' ball x r := Set.image_mono hs
  rwa [coordinateHomeomorph_image_closure_ball G hq hqpos hspan,
    coordinateHomeomorph_image_ball G hq hqpos hspan] at hi

end HeatKernel.CarnotPoint
