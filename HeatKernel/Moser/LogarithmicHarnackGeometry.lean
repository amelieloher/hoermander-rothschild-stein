-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.TentVolume
public import HeatKernel.Poincare.CarnotBallVolume
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Uniform mass comparison for the logarithmic Harnack tent -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
namespace HeatKernel

/-- The squared tent of radius three halves has at most the doubling constant
times the volume of the inner Harnack ball. -/
theorem logarithmic_harnack_tent_mass_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    (∫ y, max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal /
      (3 * r / 2)) 0 ^ 2) ≤
      (2 : ℝ)^G.homogeneousDimension *
        (CarnotPoint.volume G hq hqpos hspan).real (ball x (5 / 4 * r)) := by
  have hbig : volume (horizontalBall (G.horizontalFields hq) x (2 * (5 / 4 * r))) ≠ ⊤ :=
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x (by positivity)).ne
  have hmono : volume (horizontalBall (G.horizontalFields hq) x (3 * r / 2)) ≤
      volume (horizontalBall (G.horizontalFields hq) x (2 * (5 / 4 * r))) := by
    apply measure_mono
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hvol := ENNReal.toReal_mono hbig hmono
  rw [volume_horizontalBall_double G hq hw x (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_pow] at hvol
  norm_num only [ENNReal.toReal_ofNat] at hvol
  rw [Sobolev.integral_horizontal_tent_sq G hq hqpos hspan hw x (by positivity)]
  have hden : 2 ≤ ((G.homogeneousDimension : ℝ) + 1) *
      ((G.homogeneousDimension : ℝ) + 2) := by nlinarith [(Nat.cast_nonneg G.homogeneousDimension : (0 : ℝ) ≤ G.homogeneousDimension)]
  have hm : 2 * volume.real (horizontalBall (G.horizontalFields hq) x (3 * r / 2)) /
      (((G.homogeneousDimension : ℝ) + 1) * ((G.homogeneousDimension : ℝ) + 2)) ≤
      volume.real (horizontalBall (G.horizontalFields hq) x (3 * r / 2)) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [measureReal_nonneg (μ := volume)
      (s := horizontalBall (G.horizontalFields hq) x (3 * r / 2))]
  exact hm.trans (by
    convert hvol using 1 <;>
      first | rfl | (rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]; rfl))

end HeatKernel
