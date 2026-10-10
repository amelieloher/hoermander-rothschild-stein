-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SeparatedBallCover
public import HeatKernel.Sobolev.BallPacking
public import HeatKernel.Poincare.CarnotBallVolume
public import HeatKernel.Sobolev.BallAveraging
import Mathlib.Tactic

/-! # Equal-radius horizontal ball covers with uniform enlarged overlap -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Horizontal balls have a countable cover with disjoint half-radius balls and
at most `33^Q` overlap for the sixteenfold enlarged balls. -/
theorem exists_countable_ball_cover_overlap_sixteen {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s : ℝ} (hs : 0 < s) :
    ∃ S : Set (CarnotPoint G hq hqpos hspan), S.Countable ∧
      S.PairwiseDisjoint (fun x => ball x (s / 2)) ∧
      (⋃ x ∈ S, ball x s) = univ ∧
      ∀ x : CarnotPoint G hq hqpos hspan,
        (∑' i : S, (ball (i : CarnotPoint G hq hqpos hspan) (16 * s)).indicator
          (fun _ => (1 : ℝ≥0∞)) x) ≤ (33 : ℝ≥0∞) ^ G.homogeneousDimension := by
  let _ : SecondCountableTopology (CarnotPoint G hq hqpos hspan) :=
    inferInstanceAs (SecondCountableTopology (Fin N → ℝ))
  obtain ⟨S, hSc, hSd, hcover⟩ :=
    Sobolev.exists_countable_disjoint_half_radius_ball_cover
      (α := CarnotPoint G hq hqpos hspan) hs
  refine ⟨S, hSc, hSd, hcover, fun x => ?_⟩
  have hh : 0 < s / 2 := by positivity
  let v := MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 (s / 2))
  have hvolume (y : CarnotPoint G hq hqpos hspan) :
      volume G hq hqpos hspan (ball y (s / 2)) = v := by
    dsimp only [v]
    rw [volume_ball G hq hqpos hspan hw y hh, volume_horizontalBall G hq hw 0 hh]
  have houter (y : CarnotPoint G hq hqpos hspan) :
      volume G hq hqpos hspan (ball y (16 * s + s / 2)) ≤
        (33 : ℝ≥0∞) ^ G.homogeneousDimension * v := by
    rw [volume_ball G hq hqpos hspan hw y (by positivity)]
    change _ ≤ (33 : ℝ≥0∞) ^ G.homogeneousDimension *
      MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 (s / 2))
    rw [volume_horizontalBall G hq hw 0 hh,
      show 16 * s + s / 2 = 33 * (s / 2) by ring, mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 33),
      ENNReal.ofReal_ofNat, mul_assoc]
  exact Sobolev.tsum_indicator_ball_le_of_disjoint_equal_volume
    (μ := volume G hq hqpos hspan) (fun i : S => (i : CarnotPoint G hq hqpos hspan))
    (volume_horizontalBall_pos G hq hqpos hspan 0 hh).ne'
    (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 hh.le).ne
    (fun i j hij => hSd i.property j.property (fun he => hij (Subtype.ext he)))
    (fun i => hvolume i) houter x

end HeatKernel.CarnotPoint
