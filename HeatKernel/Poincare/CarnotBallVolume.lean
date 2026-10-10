-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.BallVolume

/-! Exact horizontal ball volume in the metric coordinate carrier. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel.CarnotPoint

/-- The metric ball in the horizontal coordinate carrier is the literal horizontal ball. -/
theorem ball_eq_horizontalBall {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) (r : ℝ) :
    ball x r = horizontalBall (G.horizontalFields hq) x r := by
  ext y
  let x₀ : Fin N → ℝ := x
  let y₀ : Fin N → ℝ := y
  have he : edist y x = horizontalL2Distance (G.horizontalFields hq) y₀ x₀ := rfl
  change dist y x < r ↔ horizontalL2Distance (G.horizontalFields hq) x₀ y₀ < ENNReal.ofReal r
  rw [← edist_lt_ofReal, he, horizontalL2Distance_comm]

/-- Metric balls have exact polynomial volume, with the volume of the unit ball at the
identity as the normalization factor. -/
theorem volume_ball {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    CarnotPoint.volume G hq hqpos hspan (ball x r) =
      ENNReal.ofReal (r ^ G.homogeneousDimension) *
        MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 1) := by
  rw [ball_eq_horizontalBall G hq hqpos hspan x r]
  exact volume_horizontalBall G hq hw x hr

/-- The real volume of a metric ball is the real volume of the unit ball at the identity
times the homogeneous power of the radius. -/
theorem volumeReal_ball {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    (CarnotPoint.volume G hq hqpos hspan).real (ball x r) =
      MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 1) *
        r ^ G.homogeneousDimension := by
  change (CarnotPoint.volume G hq hqpos hspan (ball x r)).toReal = _
  rw [volume_ball G hq hqpos hspan hw x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  exact mul_comm _ _

end HeatKernel.CarnotPoint
