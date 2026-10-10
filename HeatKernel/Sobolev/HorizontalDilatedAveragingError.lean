-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.DilatedBallAverageError
public import HeatKernel.Sobolev.HorizontalEnlargedBallCover
public import HeatKernel.Sobolev.HorizontalSignedAveraging
import Mathlib.Tactic

/-! # Horizontal averaging error under a dilated Poincaré hypothesis -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal NNReal
namespace HeatKernel.CarnotPoint

/-- Dilated Poincaré estimates imply the squared L² error estimate for the
literal signed horizontal ball average. -/
theorem eLpNorm_signed_ballAverage_error_sq_le_of_dilated_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s : ℝ} (hs : 0 < s) {P : ℝ≥0∞}
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f)
    (hfi : Integrable f (volume G hq hqpos hspan))
    (hf₂ : Integrable (fun x => f x ^ 2) (volume G hq hqpos hspan))
    {g : CarnotPoint G hq hqpos hspan → ℝ≥0∞} (hg : Measurable g)
    (hpoincare : ∀ x : CarnotPoint G hq hqpos hspan,
      (∫⁻ y in ball x (4 * s), ENNReal.ofReal ((f y -
        (∫ z in ball x (4 * s), f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x (4 * s))) ^ 2) ∂volume G hq hqpos hspan) ≤
      P * ENNReal.ofReal (4 * s) ^ 2 * ∫⁻ y in ball x (16 * s), g y ∂volume G hq hqpos hspan) :
    eLpNorm (fun x => f x -
      (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
        MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan) ^ 2 ≤
      (4 * P * ENNReal.ofReal (4 * s) ^ 2) * (33 : ℝ≥0∞) ^ G.homogeneousDimension *
        ∫⁻ x, g x ∂volume G hq hqpos hspan := by
  let _ : SecondCountableTopology (CarnotPoint G hq hqpos hspan) :=
    inferInstanceAs (SecondCountableTopology (Fin N → ℝ))
  let _ : SFinite (volume G hq hqpos hspan) :=
    inferInstanceAs (SFinite (MeasureTheory.volume : Measure (Fin N → ℝ)))
  obtain ⟨S, hSc, _, hcover, hoverlap⟩ := exists_countable_ball_cover_overlap_sixteen G hq hqpos hspan hw hs
  let _ : Countable S := hSc.to_subtype
  have hvolume (x : CarnotPoint G hq hqpos hspan) :
      volume G hq hqpos hspan (ball x s) =
        MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 s) := by
    rw [volume_ball G hq hqpos hspan hw x hs, volume_horizontalBall G hq hw 0 hs]
  have hc : (⋃ i : S, ball (i : CarnotPoint G hq hqpos hspan) s) = univ := by
    simpa only [iUnion_subtype] using hcover
  have H := Sobolev.lintegral_signed_ballAverage_error_le_of_cover_dilated_poincare
    (μ := volume G hq hqpos hspan) (fun i : S => (i : CarnotPoint G hq hqpos hspan)) hs
    (volume_horizontalBall_pos G hq hqpos hspan 0 hs).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 hs.le).ne hvolume hc hoverlap
    hf hfi hf₂ hg (fun i => hpoincare i)
  have hm : AEStronglyMeasurable (fun x => f x -
      (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
        MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s))
      (volume G hq hqpos hspan) :=
    (hf.sub (Sobolev.measurable_signed_ballAverage (μ := volume G hq hqpos hspan) s _ hf)).aestronglyMeasurable
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hm
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at he
  simp_rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] at he
  rw [he]
  exact H

end HeatKernel.CarnotPoint
