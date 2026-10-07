-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationWords

/-!
# Words of weight at most two

Bookkeeping for the base Sobolev estimate (BB pp. 585-587): in a drift alphabet (`w 0 = 2`, `w (l + 1) = 1`) every word of
weight exactly two is the drift word `[0]` or a horizontal pair `[i + 1, j + 1]`
(`eq_zero_or_pair_of_mem_wordsOfWeight_two`), and the Sobolev sum over the words of weight at
most two is bounded by the three sums over the words of weight exactly `0`, `1`, `2`
(`sum_wordFamily_two_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.P2

open RothschildStein

section Union

/-- A sum over a union is at most the sum of the two sums (values in `ℝ≥0∞`). -/
theorem sum_union_le_add {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ≥0∞) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter (s₁ := s) (s₂ := t)]
  exact le_self_add

/-- The sum over the words of weight at most two is at most the three sums over the words of
weight exactly `0`, `1` and `2`. -/
theorem sum_wordFamily_two_le {k : ℕ} (w : Fin k → ℕ+) (f : List (Fin k) → ℝ≥0∞) :
    ∑ I ∈ wordFamily w 2, f I ≤
      ∑ I ∈ wordsOfWeight w 0, f I + ∑ I ∈ wordsOfWeight w 1, f I +
        ∑ I ∈ wordsOfWeight w 2, f I := by
  classical
  have hsub : wordFamily w 2 ⊆ (wordsOfWeight w 0 ∪ wordsOfWeight w 1) ∪ wordsOfWeight w 2 := by
    intro I hI
    rw [S.mem_wordFamily_iff] at hI
    simp only [Finset.mem_union, mem_wordsOfWeight]
    omega
  calc ∑ I ∈ wordFamily w 2, f I
      ≤ ∑ I ∈ (wordsOfWeight w 0 ∪ wordsOfWeight w 1) ∪ wordsOfWeight w 2, f I :=
        Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ I ∈ wordsOfWeight w 0 ∪ wordsOfWeight w 1, f I + ∑ I ∈ wordsOfWeight w 2, f I :=
        sum_union_le_add _ _ f
    _ ≤ _ := add_le_add (sum_union_le_add _ _ f) le_rfl

end Union

section Drift

variable {q : ℕ} {w : Fin (q + 1) → ℕ+}

/-- In a drift alphabet a word of weight two is the drift word `[0]` or a horizontal pair
`[i + 1, j + 1]`. -/
theorem eq_zero_or_pair_of_mem_wordsOfWeight_two (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (hw0 : (w 0 : ℕ) = 2) {I : List (Fin (q + 1))} (hI : I ∈ wordsOfWeight w 2) :
    I = [0] ∨ ∃ i j : Fin q, I = [i.succ, j.succ] := by
  rw [mem_wordsOfWeight] at hI
  have hlen := S.length_le_wordWeight w I
  rcases I with _ | ⟨i, _ | ⟨j, _ | ⟨l, I'⟩⟩⟩
  · simp [wordWeight] at hI
  · simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hI
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
    · exact Or.inl rfl
    · have := hw l
      omega
  · simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hI
    have hi := (w i).pos
    have hj := (w j).pos
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨l, rfl⟩
    · omega
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l', rfl⟩
      · omega
      · exact Or.inr ⟨l, l', rfl⟩
  · simp at hlen
    omega

end Drift

end RothschildStein.P2
