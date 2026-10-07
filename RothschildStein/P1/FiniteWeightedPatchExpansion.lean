-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiniteHadamardPatchLowerWeight
public import RothschildStein.P1.FiniteWeightedExpansion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RothschildStein.P1

/-- Vanishing weighted jets remove every
polynomial term below that weight on the endpoint patch K. No jets
outside K are required in this actual finite expansion. -/
theorem exists_finite_hadamard_expansion_patch_lower_weight {N : ℕ} {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [LocallyCompactSpace P]
    (G : HomogeneousGroup N) (K : Set P) (b low : ℕ)
    (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hjet : ∀ p ∈ K, ∀ I : List (Fin N), (I.map G.weight).sum < low →
      rsPartial I (fun u => F (p, u)) 0 = 0) :
    ∃ poly : List (List (Fin N) × (P → ℝ)),
    ∃ rem : List (List (Fin N) × (P × (Fin N → ℝ) → ℝ)),
      (∀ q ∈ poly, q.1.length < b ∧ low ≤ (q.1.map G.weight).sum ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      (∀ q ∈ rem, q.1.length = b ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      ∀ p ∈ K, ∀ u, F (p, u) =
        (poly.map (fun q => taylorWordMonomial q.1 u * q.2 p)).sum +
        (rem.map (fun q => taylorWordMonomial q.1 u * q.2 (p, u))).sum := by
  classical
  obtain ⟨poly, rem, hp, hr, he⟩ := exists_finite_hadamard_expansion_with_patch_lower_weight G K b low F hF hjet
  let good := poly.filter (fun q => decide (low ≤ (q.1.map G.weight).sum))
  refine ⟨good, rem, ?_, hr, ?_⟩
  · intro q hq
    have hm := List.mem_filter.mp hq
    exact ⟨(hp q hm.1).1, of_decide_eq_true hm.2, (hp q hm.1).2.2⟩
  · intro p hpK u
    have hbad : ((poly.filter (fun q => ¬low ≤ (q.1.map G.weight).sum)).map
        (fun q => taylorWordMonomial q.1 u * q.2 p)).sum = 0 := by
      apply List.sum_eq_zero
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      have hm := List.mem_filter.mp hq
      have hn : ¬low ≤ (q.1.map G.weight).sum := of_decide_eq_true hm.2
      have hz : q.2 p = 0 := ((hp q hm.1).2.1.resolve_left hn) p hpK
      rw [hz]
      exact mul_zero _
    have hs := List.sum_map_filter_add_sum_map_filter_not
      (fun q : List (Fin N) × (P → ℝ) => low ≤ (q.1.map G.weight).sum)
      (fun q => taylorWordMonomial q.1 u * q.2 p) poly
    rw [hbad, add_zero] at hs
    rw [he p u]
    exact congrArg (fun z => z + (rem.map (fun q => taylorWordMonomial q.1 u * q.2 (p, u))).sum) hs.symm

/-- The constructed weighted polynomial has
exactly the required lower weight from vanishing jets and an arbitrary
upper Taylor cutoff. Every discarded high term is a smooth finite
remainder of weight at least that cutoff. -/
theorem exists_finite_weighted_expansion_patch_lower_weight {N : ℕ} {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [LocallyCompactSpace P]
    (G : HomogeneousGroup N) (K : Set P) (b low : ℕ)
    (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hjet : ∀ p ∈ K, ∀ I : List (Fin N), (I.map G.weight).sum < low →
      rsPartial I (fun u => F (p, u)) 0 = 0) :
    ∃ poly : List (List (Fin N) × (P → ℝ)),
    ∃ rem : List (List (Fin N) × (P × (Fin N → ℝ) → ℝ)),
      (∀ q ∈ poly, low ≤ (q.1.map G.weight).sum ∧
        (q.1.map G.weight).sum < b ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      (∀ q ∈ rem, b ≤ (q.1.map G.weight).sum ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      ∀ p ∈ K, ∀ u, F (p, u) =
        (poly.map (fun q => taylorWordMonomial q.1 u * q.2 p)).sum +
        (rem.map (fun q => taylorWordMonomial q.1 u * q.2 (p, u))).sum := by
  classical
  obtain ⟨poly, rem, hp, hr, he⟩ := exists_finite_hadamard_expansion_patch_lower_weight G K b low F hF hjet
  let lo := poly.filter (fun q => decide ((q.1.map G.weight).sum < b))
  let hi := poly.filter (fun q => decide (¬(q.1.map G.weight).sum < b))
  let hi₁ := hi.map (fun q => (q.1, fun z : P × (Fin N → ℝ) => q.2 z.1))
  refine ⟨lo, hi₁ ++ rem, ?_, ?_, ?_⟩
  · intro q hq
    have hm := List.mem_filter.mp hq
    exact ⟨(hp q hm.1).2.1, of_decide_eq_true hm.2, (hp q hm.1).2.2⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
      have hm := List.mem_filter.mp ha
      exact ⟨le_of_not_gt (of_decide_eq_true hm.2), ((hp a hm.1).2.2).comp contDiff_fst⟩
    · exact ⟨(hr q hq).1.symm.le.trans (taylorWord_length_le_weight G q.1), (hr q hq).2⟩
  · intro p hpK u
    have hs := List.sum_map_filter_add_sum_map_filter_not
      (fun q : List (Fin N) × (P → ℝ) => (q.1.map G.weight).sum < b)
      (fun q => taylorWordMonomial q.1 u * q.2 p) poly
    have hh : (hi₁.map (fun q => taylorWordMonomial q.1 u * q.2 (p, u))).sum =
        (hi.map (fun q => taylorWordMonomial q.1 u * q.2 p)).sum := by
      simp only [hi₁, List.map_map, Function.comp_def]
    simp only [List.map_append, List.sum_append, hh]
    rw [he p hpK u]
    change _ = (lo.map (fun q => taylorWordMonomial q.1 u * q.2 p)).sum +
      ((hi.map (fun q => taylorWordMonomial q.1 u * q.2 p)).sum + _)
    rw [← add_assoc, hs]

end RothschildStein.P1
