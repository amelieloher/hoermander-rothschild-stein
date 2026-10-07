-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WhitneySelection
public import RothschildStein.H2.Packing

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem packing_fifteen_le (D : LocDoubling X) (J : Finset X) {x : X} {r : ℝ}
    (hr : 0 < r) (hrκ : r ≤ 2 * D.κ)
    (hJ : ∀ z ∈ J, z ∈ D.Ω₁ ∧ z ∈ ball x r)
    (hsep : ∀ z ∈ J, ∀ w ∈ J, z ≠ w → r / 15 ≤ dist z w) :
    (J.card : ℝ) ≤ D.C_D ^ 7 := by
  have hlog : ⌈Real.logb 2 (6 * (15 : ℝ))⌉₊ ≤ 7 := by
    apply Nat.ceil_le.mpr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num)).mpr
    norm_num
  exact (D.outerPatch.packing_card J hr hrκ (by norm_num) hJ hsep).trans
    (pow_le_pow_right₀ (show 1 ≤ D.outerPatch.C_D from D.one_lt_C_D.le) hlog)

private theorem packing_five_le (D : LocDoubling X) (J : Finset X) {x : X} {r : ℝ}
    (hr : 0 < r) (hrκ : r ≤ 2 * D.κ)
    (hJ : ∀ z ∈ J, z ∈ D.Ω₁ ∧ z ∈ ball x r)
    (hsep : ∀ z ∈ J, ∀ w ∈ J, z ≠ w → r / 5 ≤ dist z w) :
    (J.card : ℝ) ≤ D.C_D ^ 5 := by
  have hlog : ⌈Real.logb 2 (6 * (5 : ℝ))⌉₊ ≤ 5 := by
    apply Nat.ceil_le.mpr
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num)).mpr
    norm_num
  exact (D.outerPatch.packing_card J hr hrκ (by norm_num) hJ hsep).trans
    (pow_le_pow_right₀ (show 1 ≤ D.outerPatch.C_D from D.one_lt_C_D.le) hlog)

/-- Every finite collection of selected balls containing a fixed
point has cardinality at most C_D⁷+C_D⁵ (BB Lemma 7.33, p. 322,
with the κ/5 radius cap). -/
theorem LocDoubling.whitney_overlap_card (D : LocDoubling X) {A u : Set X}
    (hA : IsOpen A) (hne : Aᶜ.Nonempty) (hu : u ⊆ A) (hA₁ : A ⊆ D.Ω₁)
    (hd : u.PairwiseDisjoint (fun z => ball z (whitneyRadius A D.κ z / 5)))
    (J : Finset X) {x : X} (hJ : ∀ z ∈ J, z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)) :
    (J.card : ℝ) ≤ D.C_D ^ 7 + D.C_D ^ 5 := by
  classical
  let J₁ := J.filter (fun z => whitneyRadius A D.κ z ≠ D.κ / 5)
  let J₂ := J.filter (fun z => whitneyRadius A D.κ z = D.κ / 5)
  have hp (z : X) (hz : z ∈ u) := (whitneyRadius_pos_le hA hne D.κ_pos (hu hz)).1
  have hs {z w : X} (hz : z ∈ u) (hw : w ∈ u) (hzw : z ≠ w) :=
    whitney_centres_separated hd hp hz hw hzw
  have h₁ : (J₁.card : ℝ) ≤ D.C_D ^ 7 := by
    by_cases hnon : J₁.Nonempty
    · obtain ⟨z₀, hz₀⟩ := hnon
      have hleft {z : X} (hz : z ∈ J₁) :
          whitneyRadius A D.κ z = infDist z Aᶜ / 2 := by
        have hn := (Finset.mem_filter.mp hz).2
        exact min_eq_left (le_of_not_ge (fun h => hn (min_eq_right h)))
      have hcomp {z : X} (hz : z ∈ J₁) :=
        whitney_boundary_comparable (hleft hz) (hJ z (Finset.mem_filter.mp hz).1).2
      have hpositive : 0 < infDist x Aᶜ :=
        (hp z₀ (hJ z₀ (Finset.mem_filter.mp hz₀).1).1).trans (hcomp hz₀).1
      have hrκ : infDist x Aᶜ ≤ 2 * D.κ := by
        have hc := (hcomp hz₀).2
        have hr := (whitneyRadius_pos_le hA hne D.κ_pos
          (hu (hJ z₀ (Finset.mem_filter.mp hz₀).1).1)).2
        linarith [D.κ_pos]
      apply packing_fifteen_le D J₁ (x := x) hpositive hrκ
      · intro z hz
        have hj := hJ z (Finset.mem_filter.mp hz).1
        refine ⟨hA₁ (hu hj.1), ?_⟩
        have hm : dist x z < whitneyRadius A D.κ z := mem_ball.mp hj.2
        rw [mem_ball, dist_comm]
        exact hm.trans (hcomp hz).1
      · intro z hz w hw hzw
        have hsz := hs (hJ z (Finset.mem_filter.mp hz).1).1
          (hJ w (Finset.mem_filter.mp hw).1).1 hzw
        have hc := (hcomp hz).2
        have hm := le_max_left (whitneyRadius A D.κ z) (whitneyRadius A D.κ w)
        linarith
    · simp only [Finset.not_nonempty_iff_eq_empty] at hnon
      rw [hnon]; simp only [Finset.card_empty, Nat.cast_zero]
      exact pow_nonneg (by linarith [D.one_lt_C_D]) _
  have h₂ : (J₂.card : ℝ) ≤ D.C_D ^ 5 := by
    apply packing_five_le D J₂ (x := x) (r := D.κ / 5)
      (div_pos D.κ_pos (by norm_num)) (by linarith [D.κ_pos])
    · intro z hz
      obtain ⟨hzJ, hzcap⟩ := Finset.mem_filter.mp hz
      have hj := hJ z hzJ
      refine ⟨hA₁ (hu hj.1), ?_⟩
      rw [← hzcap]
      simpa [mem_ball, dist_comm] using hj.2
    · intro z hz w hw hzw
      obtain ⟨hzJ, hzcap⟩ := Finset.mem_filter.mp hz
      obtain ⟨hwJ, hwcap⟩ := Finset.mem_filter.mp hw
      have hsz := hs (hJ z hzJ).1 (hJ w hwJ).1 hzw
      simpa only [hzcap, hwcap, max_self] using hsz
  have hc : J₁.card + J₂.card = J.card := by
    simpa [J₁, J₂] using Finset.card_filter_add_card_filter_not
      (s := J) (p := fun z => whitneyRadius A D.κ z ≠ D.κ / 5)
  have hc' : (J₁.card : ℝ) + J₂.card = J.card := by exact_mod_cast hc
  linarith

/-- Only finitely many selected Whitney balls contain each
point, including in a non-geodesic metric space (BB Lemma 7.33, p. 322). -/
theorem LocDoubling.whitney_overlap_finite (D : LocDoubling X) {A u : Set X}
    (hA : IsOpen A) (hne : Aᶜ.Nonempty) (hu : u ⊆ A) (hA₁ : A ⊆ D.Ω₁)
    (hd : u.PairwiseDisjoint (fun z => ball z (whitneyRadius A D.κ z / 5))) (x : X) :
    {z ∈ u | x ∈ ball z (whitneyRadius A D.κ z)}.Finite := by
  classical
  by_contra hinf
  obtain ⟨n, hn⟩ := exists_nat_gt (D.C_D ^ 7 + D.C_D ^ 5)
  obtain ⟨J, hJ, hc⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have hb := D.whitney_overlap_card hA hne hu hA₁ hd J (fun z hz => hJ hz)
  rw [hc] at hb
  exact hn.not_ge hb

/-- The literal pointwise indicator-sum overlap bound,
with the explicit constant C_D⁷+C_D⁵ (BB Lemma 7.33, p. 322). -/
theorem LocDoubling.whitney_overlap_sum (D : LocDoubling X) {A u : Set X}
    (hA : IsOpen A) (hne : Aᶜ.Nonempty) (hu : u ⊆ A) (hA₁ : A ⊆ D.Ω₁)
    (hd : u.PairwiseDisjoint (fun z => ball z (whitneyRadius A D.κ z / 5))) (x : X) :
    (∑' z : X, if z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)
      then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5) := by
  classical
  let v := {z ∈ u | x ∈ ball z (whitneyRadius A D.κ z)}
  have hv : v.Finite := D.whitney_overlap_finite hA hne hu hA₁ hd x
  let J := hv.toFinset
  have hb := D.whitney_overlap_card hA hne hu hA₁ hd J
    (fun z hz => by simpa only [J, Set.Finite.mem_toFinset, v, mem_ofPred_eq] using hz)
  have he : (∑' z : X, if z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)
      then (1 : ℝ≥0∞) else 0) = J.card := by
    rw [tsum_eq_sum (s := J) (fun z hz => by
      have hn : ¬ (z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)) := by
        simpa only [J, Set.Finite.mem_toFinset, v, mem_ofPred_eq] using hz
      simp only [ite_eq_right hn])]
    have hh : ∀ z ∈ J, (if z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)
        then (1 : ℝ≥0∞) else 0) = 1 := by
      intro z hz
      rw [ite_eq_left (by simpa only [J, Set.Finite.mem_toFinset, v, mem_ofPred_eq] using hz)]
    rw [Finset.sum_congr rfl hh]
    simp
  rw [he, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hb

end RothschildStein.H2
