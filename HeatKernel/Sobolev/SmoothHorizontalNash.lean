-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalNashFromError
public import HeatKernel.Sobolev.SmoothHorizontalAveragingErrorNorm
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint

/-! # Local Nash estimates for smooth horizontal functions -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- The local Nash estimate with explicit constants and normalized energy and first moment. -/
theorem norm_sq_le_nash_of_contDiff {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r ν : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (hQ : (G.homogeneousDimension : ℝ) ≤ ν)
    (f : CarnotPoint G hq hqpos hspan → ℝ)
    (hf : ContDiff ℝ 1 (fun x : Fin N → ℝ => f x))
    (hf₁ : MemLp f 1 (volume G hq hqpos hspan))
    (hf₂ : MemLp f 2 (volume G hq hqpos hspan))
    (hfinite : (∫⁻ x, ENNReal.ofReal
      ((horizontalGradientNorm (G.horizontalFields hq) f x) ^ 2)
        ∂volume G hq hqpos hspan) ≠ ⊤) :
    ‖hf₂.toLp f‖ ^ 2 ≤
      ((Real.sqrt (576 * (66 : ℝ) ^ G.homogeneousDimension) + 2) ^ 2 *
        2 ^ (ν / (ν + 2))) *
      (r ^ 2 * (∫⁻ x, ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) f x) ^ 2) ∂volume G hq hqpos hspan).toReal + ‖hf₂.toLp f‖ ^ 2) ^
        (ν / (ν + 2)) *
      (Real.sqrt ((MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
        (eLpNorm f 1 (volume G hq hqpos hspan)).toReal ^ 2)) ^ (4 / (ν + 2)) := by
  let K := 576 * (66 : ℝ) ^ G.homogeneousDimension
  let e := (∫⁻ x, ENNReal.ofReal ((horizontalGradientNorm (G.horizontalFields hq) f x) ^ 2) ∂volume G hq hqpos hspan).toReal
  let m := (MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
    (eLpNorm f 1 (volume G hq hqpos hspan)).toReal ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have he : 0 ≤ e := ENNReal.toReal_nonneg
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hC : 1 ≤ 1 + Real.sqrt K := by linarith [Real.sqrt_nonneg K]
  have hD : 0 ≤ r * Real.sqrt e := by positivity
  have hcoef : K ≤ (1 + Real.sqrt K) ^ 2 := by
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K]
  have hDs : (r * Real.sqrt e) ^ 2 = r ^ 2 * e := by
    rw [mul_pow, Real.sq_sqrt he]
  have herr : 576 * (66 : ℝ) ^ G.homogeneousDimension * r ^ 2 * e ≤
      (1 + Real.sqrt K) ^ 2 * (r * Real.sqrt e) ^ 2 := by
    rw [hDs]
    exact (by simpa only [K, mul_assoc] using
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg r) he))
  have hfm : Measurable (f : CarnotPoint G hq hqpos hspan → ℝ) :=
    hf.continuous.measurable
  have herrors : ∀ s : ℝ, 0 < s →
      (eLpNorm (fun x : CarnotPoint G hq hqpos hspan => f x -
        (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
          MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
            (volume G hq hqpos hspan)).toReal ^ 2 ≤ K * s ^ 2 * e := by
    intro s hs
    exact (memLp_and_error_sq_le_of_contDiff G hq hqpos hspan hw hs f hf
      (memLp_one_iff_integrable.mp hf₁) hf₂.integrable_sq hfinite).2
  have H := norm_sq_le_nash_of_signed_average_error G hq hqpos hspan hw hr hC hD
    (Real.sqrt_nonneg m) hν hQ hfm hf₁ hf₂ herrors herr
    (by change m ≤ (Real.sqrt m) ^ 2; rw [Real.sq_sqrt hm])
    (E := r ^ 2 * e + ‖hf₂.toLp f‖ ^ 2) (by rw [hDs])
  have hsum : 1 + Real.sqrt K + 1 = Real.sqrt K + 2 := by ring
  simpa only [hsum, K, e, m] using H

end HeatKernel.CarnotPoint
