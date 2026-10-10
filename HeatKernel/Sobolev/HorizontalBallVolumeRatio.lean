-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotBallVolume
public import HeatKernel.Sobolev.BallAveraging
import Mathlib.Tactic

/-! # Ordinary volume ratios for horizontal layer balls -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- The ordinary volume ratio of two concentric horizontal balls is the radius ratio to dimension. -/
theorem volumeReal_ball_div {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (volume G hq hqpos hspan).real (ball x s) /
      (volume G hq hqpos hspan).real (ball x r) = (s / r) ^ G.homogeneousDimension := by
  have hv : 0 < MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 1) :=
    ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan 0 (by norm_num)).ne'
      (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by norm_num)).ne
  rw [volumeReal_ball G hq hqpos hspan hw x hs, volumeReal_ball G hq hqpos hspan hw x hr,
    div_pow]
  field_simp

/-- Every layer between the half-ball and the full ball has volume ratio at most two to dimension. -/
theorem volumeReal_layer_ball_div_half_le {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (ht₁ : t ≤ 1) :
    (volume G hq hqpos hspan).real (ball x (t * r)) /
      (volume G hq hqpos hspan).real (ball x (r / 2)) ≤ (2 : ℝ) ^ G.homogeneousDimension := by
  rw [volumeReal_ball_div G hq hqpos hspan hw x (mul_pos ht hr) (by positivity)]
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ (by positivity : 0 < r / 2)).mpr
  nlinarith

end HeatKernel.CarnotPoint
