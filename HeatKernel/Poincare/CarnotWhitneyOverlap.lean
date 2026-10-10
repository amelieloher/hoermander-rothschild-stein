-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotWhitneyCover
public import HeatKernel.Poincare.CarnotBallVolume
public import HeatKernel.Poincare.WhitneyOverlapPacking
public import Mathlib.Data.Set.Card

/-! Countable Whitney covers with quantitative overlap for horizontal metric balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped ENNReal

namespace HeatKernel.CarnotPoint

/-- Horizontal metric balls have exact boundary-distance Whitney covers with eightyfold
interior containment and overlap at most 1000^Q. -/
theorem exists_countable_boundaryBall_cover_with_overlap {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r κ : ℝ} (hr : 0 < r) (hκ : 240 < κ) :
    ∃ C : Set (CarnotPoint G hq hqpos hspan), C ⊆ ball x r ∧ C.Countable ∧
      (C.PairwiseDisjoint fun z => ball z (infDist z (ball x r)ᶜ / κ)) ∧
      ball x r = ⋃ z ∈ C, ball z (5 * (infDist z (ball x r)ᶜ / κ)) ∧
      (∀ z ∈ C, ball z (80 * (infDist z (ball x r)ᶜ / κ)) ⊆ ball x r) ∧
      ∀ y, {z ∈ C | y ∈ ball z (80 * (infDist z (ball x r)ᶜ / κ))}.Finite ∧
        {z ∈ C | y ∈ ball z (80 * (infDist z (ball x r)ᶜ / κ))}.ncard ≤
          1000 ^ G.homogeneousDimension := by
  classical
  let μ := CarnotPoint.volume G hq hqpos hspan
  let v := MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 1)
  have hv0 : v ≠ 0 := (volume_horizontalBall_pos G hq hqpos hspan 0 zero_lt_one).ne'
  have hvtop : v ≠ ⊤ := (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 zero_le_one).ne
  have hvolume : ∀ z : CarnotPoint G hq hqpos hspan, ∀ s : ℝ, 0 < s →
      μ (ball z s) = ENNReal.ofReal (s ^ G.homogeneousDimension) * v :=
    fun z s hs => volume_ball G hq hqpos hspan hw z hs
  have hcompl : (ball x r)ᶜ.Nonempty := by
    obtain ⟨w, hw'⟩ := exists_dist_eq G hq hqpos hspan hw x hr
    refine ⟨w, ?_⟩
    change ¬ dist w x < r
    rw [dist_comm, hw']
    exact lt_irrefl r
  obtain ⟨C, hCU, hcount, hdisj, hcover, hinterior⟩ :=
    exists_countable_disjoint_boundaryBall_cover G hq hqpos hspan hw x hr (by linarith)
  refine ⟨C, hCU, hcount, hdisj, hcover, hinterior, ?_⟩
  intro y
  let I := {z ∈ C | y ∈ ball z (80 * (infDist z (ball x r)ᶜ / κ))}
  have hfinite : I.Finite := boundaryBall_overlap_finite μ G.homogeneousDimension v hv0 hvtop
    hvolume isOpen_ball hcompl hCU hκ hdisj y
  refine ⟨hfinite, ?_⟩
  have hb := boundaryBall_overlap_card μ G.homogeneousDimension v hv0 hvtop hvolume
    isOpen_ball hcompl hCU hκ hdisj hfinite.toFinset y
    (fun z hz => hfinite.mem_toFinset.mp hz)
  rw [Set.ncard_eq_toFinset_card I hfinite]
  exact hb.trans (pow_le_pow_left₀ (Nat.zero_le 324) (by norm_num : 324 ≤ 1000) _)

end HeatKernel.CarnotPoint
