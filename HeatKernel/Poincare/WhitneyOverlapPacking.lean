-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyComparability
public import HeatKernel.Poincare.HomogeneousPacking

/-! Quantitative overlap bounds for exact boundary-distance Whitney balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Exact homogeneous ball volumes bound the number of eightyfold Whitney dilates
containing one point by 324^Q, for any separation constant greater than 240. -/
theorem boundaryBall_overlap_card {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    {U C : Set E} (hU : IsOpen U) (hcompl : Uᶜ.Nonempty) (hCU : C ⊆ U)
    {κ : ℝ} (hκ : 240 < κ)
    (hdisj : C.PairwiseDisjoint fun z => ball z (infDist z Uᶜ / κ))
    (s : Finset E) (y : E)
    (hs : ∀ z ∈ s, z ∈ C ∧ y ∈ ball z (80 * (infDist z Uᶜ / κ))) : s.card ≤ 324 ^ Q := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    let a := fun z : E => infDist z Uᶜ / κ
    have hk : 0 < κ := by linarith
    have ha₀ : 0 < a z₀ := div_pos
      ((hU.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
        (by simpa using hCU (hs z₀ hz₀).1)) hk
    have hcompare : ∀ z ∈ s, a z ≤ 2 * a z₀ ∧ a z₀ ≤ 2 * a z := by
      intro z hz
      exact boundaryBall_radii_comparable_of_dilates_intersect U (by norm_num) (by nlinarith)
        ⟨y, (hs z hz).2, (hs z₀ hz₀).2⟩
    apply card_le_of_homogeneous_ball_packing μ Q v hv0 hvtop hvolume s id a y
      (div_pos ha₀ (by norm_num : (0 : ℝ) < 2)) 324 (by norm_num)
    · intro z hz w hw hzw
      exact hdisj (hs z hz).1 (hs w hw).1 hzw
    · intro z hz
      have hh := (hcompare z hz).2
      linarith
    · intro z hz
      have hh := ball_subset_of_common_dilate_point (by norm_num : (0 : ℝ) ≤ 80)
        (hcompare z hz).1 (hs z hz).2
      have he : (2 * (80 : ℝ) + 2) * a z₀ = (324 : ℝ) * (a z₀ / 2) := by ring
      rw [he] at hh
      exact hh
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Nat.zero_le _

/-- Only finitely many eightyfold dilates of a disjoint exact Whitney family contain
a given point in an exact homogeneous-volume metric space. -/
theorem boundaryBall_overlap_finite {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    {U C : Set E} (hU : IsOpen U) (hcompl : Uᶜ.Nonempty) (hCU : C ⊆ U)
    {κ : ℝ} (hκ : 240 < κ)
    (hdisj : C.PairwiseDisjoint fun z => ball z (infDist z Uᶜ / κ)) (y : E) :
    {z ∈ C | y ∈ ball z (80 * (infDist z Uᶜ / κ))}.Finite := by
  classical
  by_contra hinf
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (324 ^ Q + 1)
  have hb := boundaryBall_overlap_card μ Q v hv0 hvtop hvolume hU hcompl hCU hκ hdisj s y
    (fun z hz => hs hz)
  exact (Nat.lt_succ_self (324 ^ Q)).not_ge (by simpa only [hcard] using hb)

end HeatKernel
