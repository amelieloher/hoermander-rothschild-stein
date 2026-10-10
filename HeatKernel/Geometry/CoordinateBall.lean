-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.BallVolume

/-! Horizontal metric balls as open subsets of the coordinate calculus space. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- The horizontal metric ball viewed as a coordinate open set. -/
def coordinateBall {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) (r : ℝ) : Opens (Fin N → ℝ) :=
  ⟨@Metric.ball (CarnotPoint G hq hqpos hspan) _ x r,
    Metric.isOpen_ball (α := CarnotPoint G hq hqpos hspan)⟩

/-- Coordinate balls agree with the literal extended-distance balls. -/
theorem coordinateBall_eq_horizontalBall {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) (r : ℝ) :
    (coordinateBall G hq hqpos hspan x r : Set (Fin N → ℝ)) =
      horizontalBall (G.horizontalFields hq) x r := by
  ext y
  change dist (show CarnotPoint G hq hqpos hspan from y) x < r ↔
    horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r
  rw [← edist_lt_ofReal, edist_comm, edist_eq]

end HeatKernel.CarnotPoint
