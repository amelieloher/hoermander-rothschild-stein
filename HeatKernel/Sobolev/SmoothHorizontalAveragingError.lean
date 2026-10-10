-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalDilatedAveragingError
public import HeatKernel.Poincare.SmoothWeakPoincare
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all HeatKernel.Geometry.CarnotPoint

/-! # Signed horizontal averaging errors for smooth functions -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Smooth horizontal averaging error follows from the dilation-four Poincaré inequality. -/
theorem eLpNorm_signed_ballAverage_error_sq_le_of_contDiff {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s : ℝ} (hs : 0 < s) (u : (Fin N → ℝ) → ℝ) (hu : ContDiff ℝ 1 u)
    (hfi : Integrable u (volume G hq hqpos hspan))
    (hf₂ : Integrable (fun y => u y ^ 2) (volume G hq hqpos hspan)) :
    eLpNorm (fun x : CarnotPoint G hq hqpos hspan => u x -
      (∫ y in ball x s, u y ∂volume G hq hqpos hspan) /
        MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan) ^ 2 ≤
      (4 * (9 * (2 : ℝ≥0∞) ^ G.homogeneousDimension) * ENNReal.ofReal (4 * s) ^ 2) *
        (33 : ℝ≥0∞) ^ G.homogeneousDimension * ∫⁻ y,
          ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u y) ^ 2)
            ∂volume G hq hqpos hspan := by
  have hf : Measurable (u : CarnotPoint G hq hqpos hspan → ℝ) :=
    hu.continuous.measurable
  have hgc : Continuous (horizontalGradientNorm (G.horizontalFields hq) u) :=
    continuousOn_univ.mp (continuousOn_horizontalGradientNorm
      (fun i => (G.horizontalFields_contDiff hq i).continuous) isOpen_univ hu.contDiffOn)
  have hg : Measurable (fun y : CarnotPoint G hq hqpos hspan =>
      ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u y) ^ 2)) := by
    change Measurable (fun y : Fin N → ℝ =>
      ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) u y) ^ 2))
    exact ENNReal.continuous_ofReal.measurable.comp (hgc.pow 2).measurable
  apply eLpNorm_signed_ballAverage_error_sq_le_of_dilated_poincare G hq hqpos hspan hw
    hs hf hfi hf₂ hg
  intro x
  have H := HeatKernel.lintegral_weak_horizontalPoincare G hq hqpos hspan hw x
    (r := 4 * s) (p := 2) (by positivity) (by norm_num) u univ isOpen_univ
    (subset_univ _) hu.contDiffOn
  have hmean : (⨍ y in horizontalBall (G.horizontalFields hq) x (4 * s), u y) =
      (∫ y in horizontalBall (G.horizontalFields hq) x (4 * s), u y) /
        MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) x (4 * s)) := by
    rw [setAverage_eq, smul_eq_mul]
    ring
  have hcoef : (2 : ℝ≥0∞) ^ G.homogeneousDimension * ENNReal.ofReal ((3 * (4 * s)) ^ 2) =
      (9 * (2 : ℝ≥0∞) ^ G.homogeneousDimension) * ENNReal.ofReal (4 * s) ^ 2 := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ 2),
      ENNReal.ofReal_pow (by positivity : 0 ≤ 4 * s)]
    norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num, ENNReal.ofReal_ofNat]
    ring
  simp only [Real.rpow_two, sq_abs, hmean, hcoef, show 4 * (4 * s) = 16 * s by ring] at H
  rw [ball_eq_horizontalBall G hq hqpos hspan x (4 * s),
    ball_eq_horizontalBall G hq hqpos hspan x (16 * s)]
  convert H using 1 <;> rfl

end HeatKernel.CarnotPoint
