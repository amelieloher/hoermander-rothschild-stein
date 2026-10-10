-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NestedSetAverageExtended
public import HeatKernel.Sobolev.HorizontalBallVolumeRatio
import Mathlib.Tactic

/-! # Poincaré bounds for inner and outer horizontal tent layers -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Small layers inherit the half-ball oscillation estimate by inclusion. -/
theorem lintegral_sub_halfBallAverage_sq_le_on_small_layer {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : CarnotPoint G hq hqpos hspan) {r t : ℝ} (hr : 0 < r) (ht : t ≤ 1 / 2)
    {f : CarnotPoint G hq hqpos hspan → ℝ} {g : CarnotPoint G hq hqpos hspan → ℝ≥0∞}
    {P : ℝ≥0∞}
    (hpoincare : (∫⁻ y in ball x (r / 2), ENNReal.ofReal ((f y -
      (∫ z in ball x (r / 2), f z ∂volume G hq hqpos hspan) /
        (volume G hq hqpos hspan).real (ball x (r / 2))) ^ 2) ∂volume G hq hqpos hspan) ≤
      P * ENNReal.ofReal (r / 2) ^ 2 * ∫⁻ y in ball x (r / 2), g y ∂volume G hq hqpos hspan) :
    (∫⁻ y in ball x (t * r), ENNReal.ofReal ((f y -
      (∫ z in ball x (r / 2), f z ∂volume G hq hqpos hspan) /
        (volume G hq hqpos hspan).real (ball x (r / 2))) ^ 2) ∂volume G hq hqpos hspan) ≤
      P * ENNReal.ofReal (r / 2) ^ 2 * ∫⁻ y in ball x (r / 2), g y ∂volume G hq hqpos hspan := by
  apply (lintegral_mono_set (ball_subset_ball (by nlinarith : t * r ≤ r / 2))).trans hpoincare

/-- Outer layers satisfy Poincaré about the half-ball mean with explicit volume-ratio cost. -/
theorem lintegral_sub_halfBallAverage_sq_le_on_large_layer {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r t : ℝ} (hr : 0 < r)
    (ht : 1 / 2 ≤ t) (ht₁ : t ≤ 1)
    {f : CarnotPoint G hq hqpos hspan → ℝ}
    (hf : IntegrableOn f (ball x (t * r)) (volume G hq hqpos hspan))
    (hf₂ : IntegrableOn (fun y => f y ^ 2) (ball x (t * r)) (volume G hq hqpos hspan))
    {g : CarnotPoint G hq hqpos hspan → ℝ≥0∞} {P : ℝ≥0∞}
    (hpoincare : (∫⁻ y in ball x (t * r), ENNReal.ofReal ((f y -
      (∫ z in ball x (t * r), f z ∂volume G hq hqpos hspan) /
        (volume G hq hqpos hspan).real (ball x (t * r))) ^ 2) ∂volume G hq hqpos hspan) ≤
      P * ENNReal.ofReal (t * r) ^ 2 * ∫⁻ y in ball x (t * r), g y ∂volume G hq hqpos hspan) :
    (∫⁻ y in ball x (t * r), ENNReal.ofReal ((f y -
      (∫ z in ball x (r / 2), f z ∂volume G hq hqpos hspan) /
        (volume G hq hqpos hspan).real (ball x (r / 2))) ^ 2) ∂volume G hq hqpos hspan) ≤
      ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2 *
        ∫⁻ y in ball x (t * r), g y ∂volume G hq hqpos hspan := by
  have htpos : 0 < t := by linarith
  have hhalf : 0 < r / 2 := by positivity
  have hpos : 0 < (volume G hq hqpos hspan).real (ball x (r / 2)) := by
    change 0 < (volume G hq hqpos hspan (ball x (r / 2))).toReal
    rw [volume_ball G hq hqpos hspan hw x hhalf,
      ← volume_horizontalBall G hq hw 0 hhalf]
    exact ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan 0 hhalf).ne'
      (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 hhalf.le).ne
  have hfinite : volume G hq hqpos hspan (ball x (t * r)) ≠ ⊤ := by
    rw [ball_eq_horizontalBall G hq hqpos hspan x (t * r)]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw x (mul_nonneg htpos.le hr.le)).ne
  have hratio := volumeReal_layer_ball_div_half_le G hq hqpos hspan hw x hr htpos ht₁
  have H := Sobolev.lintegral_sub_nested_setAverage_sq_le_of_poincare
    measurableSet_ball measurableSet_ball (ball_subset_ball (by nlinarith : r / 2 ≤ t * r))
    hfinite hpos hf hf₂ (ENNReal.ofReal_le_ofReal (by linarith :
      1 + (volume G hq hqpos hspan).real (ball x (t * r)) /
        (volume G hq hqpos hspan).real (ball x (r / 2)) ≤ 1 + (2 : ℝ) ^ G.homogeneousDimension))
    hpoincare
  apply H.trans
  have hrad : ENNReal.ofReal (t * r) ^ 2 ≤ ENNReal.ofReal r ^ 2 := by
    gcongr
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hrad (show 0 ≤ (∫⁻ y in ball x (t * r), g y ∂volume G hq hqpos hspan) from zero_le))
    (show 0 ≤ ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P from zero_le)

end HeatKernel.CarnotPoint
