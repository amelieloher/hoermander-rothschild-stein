-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NormalizedBallAveraging
public import HeatKernel.Sobolev.QuadraticNormBounds
import Mathlib.Tactic

/-! # Lebesgue space representatives of horizontal ball averages -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Every measurable integrable function has an L² ball average with the normalized bound. -/
theorem exists_lp_signed_ballAverage {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s r ν : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hν : (G.homogeneousDimension : ℝ) ≤ ν)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f)
    (hf₁ : MemLp f 1 (volume G hq hqpos hspan)) :
    ∃ u : Lp ℝ 2 (volume G hq hqpos hspan),
      (⇑u =ᵐ[volume G hq hqpos hspan] fun x =>
        (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
          MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) ∧
      ‖u‖ ≤ Real.sqrt (((r / s) ^ ν) *
        (MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
        (eLpNorm f 1 (volume G hq hqpos hspan)).toReal ^ 2) := by
  have hr : 0 < r := hs.trans_le hsr
  have hv : (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (volume_horizontalBall_pos G hq hqpos hspan 0 hr).ne'
  have hfin : ENNReal.ofReal ((r / s) ^ ν) *
      (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
      eLpNorm f 1 (volume G hq hqpos hspan) ^ 2 ≠ ⊤ := by
    finiteness
  have H := eLpNorm_signed_ballAverage_sq_le_rpow G hq hqpos hspan hw hs hsr hν hf
  have ht := Sobolev.exists_lp_of_eLpNorm_sq_le ENNReal.toReal_nonneg
    (by rw [ENNReal.ofReal_toReal hfin]; exact H)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (div_nonneg hr.le hs.le) ν),
    measureReal_def] using ht

end HeatKernel.CarnotPoint
