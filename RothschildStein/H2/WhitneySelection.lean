-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WhitneyRadii
public import RothschildStein.H2.Vitali

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- (c),(d) A countable Whitney selection, with disjoint
one-fifth balls and the radius cap needed by the maximal function (BB Lemma 7.33, pp. 321–322). -/
theorem LocDoubling.whitney_selection (D : LocDoubling X) {A : Set X}
    (hA : IsOpen A) (hA₁ : A ⊆ D.Ω₁) (hne : Aᶜ.Nonempty) :
    ∃ u : Set X, u ⊆ A ∧ u.Countable ∧
      u.PairwiseDisjoint (fun x => ball x (whitneyRadius A D.κ x / 5)) ∧
      A = ⋃ x ∈ u, ball x (whitneyRadius A D.κ x) ∧
      (∀ x ∈ u, 0 < whitneyRadius A D.κ x ∧ 5 * whitneyRadius A D.κ x ≤ D.κ) ∧
      (∀ x ∈ u, ball x (4 * whitneyRadius A D.κ x) ⊆ D.Ω₂) ∧
      (∀ x ∈ u, whitneyRadius A D.κ x = D.κ / 5 ∨
        ∃ y ∉ A, dist x y < 4 * whitneyRadius A D.κ x) := by
  have hr (x : X) (hx : x ∈ A) := whitneyRadius_pos_le hA hne D.κ_pos hx
  obtain ⟨u, huA, huc, hud, hcover, _⟩ := vitali_covering_of_patch_hypotheses
    D.μ D.Ω₁ D.Ω₂ D.κ D.C_D D.κ_pos D.one_lt_C_D
    D.outerPatch.incl D.outerPatch.doubling ⟨D.open₂.measurableSet, D.finΩ₂⟩
    A (fun x => x) (fun x => whitneyRadius A D.κ x / 5)
    (fun x hx => hA₁ hx) (fun x hx => ⟨div_pos (hr x hx).1 (by norm_num), by linarith [(hr x hx).2, D.κ_pos]⟩)
  have hc : A ⊆ ⋃ x ∈ u, ball x (whitneyRadius A D.κ x) := by
    intro x hx
    have hsmall : x ∈ ⋃ y ∈ A, ball y (whitneyRadius A D.κ y / 5) :=
      mem_iUnion₂.mpr ⟨x, hx, mem_ball_self (div_pos (hr x hx).1 (by norm_num))⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hsmall)
    have he : 5 * (whitneyRadius A D.κ y / 5) = whitneyRadius A D.κ y := by ring
    rw [he] at hxy
    exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩
  refine ⟨u, huA, huc, hud, subset_antisymm hc ?_, ?_, ?_, ?_⟩
  · exact iUnion₂_subset fun x hx => whitney_ball_subset hA hne D.κ_pos (huA hx)
  · intro x hx
    exact ⟨(hr x (huA hx)).1, by linarith [(hr x (huA hx)).2]⟩
  · intro x hx
    exact (ball_subset_ball (show 4 * whitneyRadius A D.κ x ≤ 6 * D.κ by
        linarith [(hr x (huA hx)).2, D.κ_pos])).trans
      (D.outerPatch.incl x (hA₁ (huA hx)))
  · intro x hx
    exact whitney_stopping_point hA hne D.κ_pos (huA hx)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Disjoint one-fifth balls give centre separation in arbitrary
metric spaces; no geodesic assumption is needed. -/
theorem whitney_centres_separated {A : Set X} {κ : ℝ} {u : Set X}
    (hd : u.PairwiseDisjoint (fun x => ball x (whitneyRadius A κ x / 5)))
    (hp : ∀ x ∈ u, 0 < whitneyRadius A κ x) {x y : X}
    (hx : x ∈ u) (hy : y ∈ u) (hxy : x ≠ y) :
    max (whitneyRadius A κ x) (whitneyRadius A κ y) / 5 ≤ dist x y := by
  have hdisj := hd hx hy hxy
  have h1 : whitneyRadius A κ x / 5 ≤ dist x y := by
    by_contra hn
    have hym : y ∈ ball x (whitneyRadius A κ x / 5) := by
      simpa [mem_ball, dist_comm] using lt_of_not_ge hn
    exact Set.disjoint_left.mp hdisj hym (mem_ball_self (div_pos (hp y hy) (by norm_num)))
  have h2 : whitneyRadius A κ y / 5 ≤ dist x y := by
    by_contra hn
    have hxm : x ∈ ball y (whitneyRadius A κ y / 5) := by
      simpa [mem_ball] using lt_of_not_ge hn
    exact Set.disjoint_left.mp hdisj (mem_ball_self (div_pos (hp x hx) (by norm_num))) hxm
  rcases le_total (whitneyRadius A κ x) (whitneyRadius A κ y) with h | h
  · simpa only [max_eq_right h] using h2
  · simpa only [max_eq_left h] using h1

end RothschildStein.H2
