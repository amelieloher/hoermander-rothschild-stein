-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalLinearTentLayers
public import HeatKernel.Sobolev.WeightedMeanExtended
public import HeatKernel.Sobolev.TentVolume
import Mathlib.Tactic

/-! # Linear-tent horizontal Poincaré inequalities -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Same-ball Poincaré implies the linear-tent inequality with its actual normalized weighted mean. -/
theorem lintegral_tent_sub_weightedMean_le_of_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (ball x r) (volume G hq hqpos hspan))
    (hf₂ : IntegrableOn (fun y => f y ^ 2) (ball x r) (volume G hq hqpos hspan))
    {g : CarnotPoint G hq hqpos hspan → ℝ≥0∞} (hg : Measurable g) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, g y ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) *
      ENNReal.ofReal ((f y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0) f) ^ 2) ∂volume G hq hqpos hspan) ≤
      ((P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) * g y ∂volume G hq hqpos hspan := by
  let w : CarnotPoint G hq hqpos hspan → ℝ := fun y => max (1 - dist x y / r) 0
  have hwm : Measurable w := by fun_prop
  have hwn (y : CarnotPoint G hq hqpos hspan) : 0 ≤ w y := le_max_right _ _
  have hwb (y : CarnotPoint G hq hqpos hspan) : ‖w y‖ ≤ 1 := by
    have hd : 0 ≤ dist x y / r := div_nonneg dist_nonneg hr.le
    have hm : 0 ≤ max (1 - dist x y / r) 0 := le_max_right _ _
    have hl : max (1 - dist x y / r) 0 ≤ 1 := max_le (by linarith) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (hwn y)]
    dsimp [w]
    nlinarith
  have hwz (y : CarnotPoint G hq hqpos hspan) (hy : y ∉ ball x r) : w y = 0 := by
    have hd : r ≤ dist x y := by simpa only [mem_ball, not_lt, dist_comm y x] using hy
    have hz : 1 - dist x y / r ≤ 0 := by
      have hdiv : 1 ≤ dist x y / r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hd)
      linarith
    dsimp [w]
    rw [max_eq_right hz]
  have hweq : w = fun y => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0 := by
    funext y
    dsimp only [w]
    rw [dist_edist, edist_eq]
  have hwi : Integrable w (volume G hq hqpos hspan) := by
    rw [hweq]
    change Integrable (fun y : Fin N → ℝ => max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0) MeasureTheory.volume
    exact (Sobolev.integrable_horizontal_tent_and_sq G hq hqpos hspan hw x hr).1
  have hmass : 0 < ∫ y, w y ∂volume G hq hqpos hspan := by
    rw [hweq]
    change 0 < ∫ y : Fin N → ℝ, max (1 -
      (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0
    exact Sobolev.integral_horizontal_tent_pos G hq hqpos hspan hw x hr
  have hwu₂ : Integrable (fun y => w y * f y ^ 2) (volume G hq hqpos hspan) :=
    Sobolev.integrable_mul_of_bounded_support_weight measurableSet_ball hwm hwb hwz hf₂
  have H := Sobolev.lintegral_weight_mul_sub_weightedMean_sq_le hwi hf.aestronglyMeasurable
    hwn hwu₂ hmass ((∫ z in ball x (r / 2), f z ∂volume G hq hqpos hspan) /
      (volume G hq hqpos hspan).real (ball x (r / 2)))
  exact H.trans (lintegral_tent_sub_halfBallAverage_le_of_poincare G hq hqpos hspan hw x hr
    hf hfi hf₂ hg hpoincare)

end HeatKernel.CarnotPoint
