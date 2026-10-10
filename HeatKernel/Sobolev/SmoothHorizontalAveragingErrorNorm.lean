-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SmoothHorizontalAveragingError
public import HeatKernel.Sobolev.QuadraticNormBounds
import Mathlib.Tactic

/-! # Finite L² horizontal averaging errors for smooth functions -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Finite horizontal energy controls the ordinary squared averaging error of a smooth function. -/
theorem memLp_and_error_sq_le_of_contDiff {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s : ℝ} (hs : 0 < s) (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hfi : Integrable f (volume G hq hqpos hspan))
    (hf₂ : Integrable (fun x => f x ^ 2) (volume G hq hqpos hspan))
    (henergy : (∫⁻ x, ENNReal.ofReal
      ((horizontalGradientNorm (G.horizontalFields hq) f x) ^ 2)
        ∂volume G hq hqpos hspan) ≠ ⊤) :
    MemLp (fun x => f x - (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
      MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan) ∧
    (eLpNorm (fun x => f x - (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
      MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan)).toReal ^ 2 ≤
      576 * (66 : ℝ) ^ G.homogeneousDimension * s ^ 2 *
        (∫⁻ x, ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) f x) ^ 2) ∂volume G hq hqpos hspan).toReal := by
  have H := eLpNorm_signed_ballAverage_error_sq_le_of_contDiff G hq hqpos hspan hw
    hs f hf hfi hf₂
  have hfin : (4 * (9 * (2 : ℝ≥0∞) ^ G.homogeneousDimension) * ENNReal.ofReal (4 * s) ^ 2) *
      (33 : ℝ≥0∞) ^ G.homogeneousDimension * (∫⁻ x, ENNReal.ofReal
        ((horizontalGradientNorm (G.horizontalFields hq) f x) ^ 2)
          ∂volume G hq hqpos hspan) ≠ ⊤ := by finiteness
  refine ⟨Sobolev.memLp_of_eLpNorm_sq_le hfin H, ?_⟩
  have ht := ENNReal.toReal_mono hfin H
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * s)] at ht
  have hpow : (66 : ℝ) ^ G.homogeneousDimension =
      (2 : ℝ) ^ G.homogeneousDimension * (33 : ℝ) ^ G.homogeneousDimension := by
    rw [← mul_pow]; norm_num
  have hcoef : 4 * (9 * (2 : ℝ) ^ G.homogeneousDimension) * (4 * s) ^ 2 *
      (33 : ℝ) ^ G.homogeneousDimension = 576 * (66 : ℝ) ^ G.homogeneousDimension * s ^ 2 := by
    rw [hpow]
    ring
  rw [hcoef] at ht
  exact ht

end HeatKernel.CarnotPoint
