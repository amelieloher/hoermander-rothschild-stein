-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.ConvolutionLipschitz

/-! Positive dilation covariance for horizontal metric distances, closed balls, and spheres. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set RothschildStein
namespace HeatKernel.CarnotPoint

variable {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
  (hspan : bracketSpansOn univ (G.horizontalFields hq))
  (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)

include hw

/-- Positive dilations multiply the real horizontal metric distance by their factor. -/
theorem dist_dilate {r : ℝ} (hr : 0 < r) (x y : CarnotPoint G hq hqpos hspan) :
    @dist (CarnotPoint G hq hqpos hspan)
      (homogeneousHorizontalMetricSpace G hq hqpos hspan).toDist
      (G.dilate r x) (G.dilate r y) = r * dist x y := by
  unfold CarnotPoint at *
  change (horizontalL2Distance (G.horizontalFields hq) (G.dilate r x)
    (G.dilate r y)).toReal = r * (horizontalL2Distance (G.horizontalFields hq) x y).toReal
  have he := congrArg ENNReal.toReal (horizontalL2Distance_dilate G hq hw hr x y)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le] using he

end HeatKernel.CarnotPoint
