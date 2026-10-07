-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftWords

/-!
# No drift: words of weight at most two

Bookkeeping for the base Sobolev estimate (BB pp. 585-587) without drift. In a no-drift alphabet (`Fin q`, all weights
one) every word of weight exactly two is a pair `[i, j]`
(`eq_pair_of_mem_wordsOfWeight_two_noDrift`), and the Sobolev sum over the words of weight at
most two is bounded by the three sums over the words of weight exactly `0`, `1`, `2`
(`sum_wordFamily_two_le_noDrift`).
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
theorem sum_union_le_add_noDrift {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ≥0∞) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter (s₁ := s) (s₂ := t)]
  exact le_self_add

/-- The sum over the words of weight at most two is at most the three sums over the words of
weight exactly `0`, `1` and `2`. -/
theorem sum_wordFamily_two_le_noDrift {q : ℕ} (w : Fin q → ℕ+) (f : List (Fin q) → ℝ≥0∞) :
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
        sum_union_le_add_noDrift _ _ f
    _ ≤ _ := add_le_add (sum_union_le_add_noDrift _ _ f) le_rfl

end Union

section NoDrift

variable {q : ℕ} {w : Fin q → ℕ+}

/-- In a no-drift alphabet a word of weight two is a pair `[i, j]`. -/
theorem eq_pair_of_mem_wordsOfWeight_two_noDrift (hw : ∀ j, (w j : ℕ) = 1)
    {I : List (Fin q)} (hI : I ∈ wordsOfWeight w 2) : ∃ i j : Fin q, I = [i, j] := by
  rw [mem_wordsOfWeight] at hI
  have hlen := S.length_le_wordWeight w I
  rcases I with _ | ⟨i, _ | ⟨j, _ | ⟨l, I'⟩⟩⟩
  · simp [wordWeight] at hI
  · simp [wordWeight, hw i] at hI
  · exact ⟨i, j, rfl⟩
  · simp at hlen
    omega

/-- The empty word, the letters and the pairs lie in the word family of order two (no
drift). -/
theorem pair_mem_wordFamily_two_noDrift (hw : ∀ j, (w j : ℕ) = 1) (i j : Fin q) :
    [i, j] ∈ wordFamily w 2 := by
  rw [S.mem_wordFamily_iff]
  simp [wordWeight, hw i, hw j]

/-- A letter lies in the word family of order two (no drift). -/
theorem single_mem_wordFamily_two_noDrift (hw : ∀ j, (w j : ℕ) = 1) (i : Fin q) :
    [i] ∈ wordFamily w 2 := by
  rw [S.mem_wordFamily_iff]
  simp [wordWeight, hw i]

/-- A word of weight two lies in the word family of order two. -/
theorem mem_wordFamily_two_of_mem_wordsOfWeight_two_noDrift {I : List (Fin q)}
    (hI : I ∈ wordsOfWeight w 2) : I ∈ wordFamily w 2 := by
  rw [S.mem_wordFamily_iff]
  exact ((mem_wordsOfWeight w).1 hI).le

end NoDrift

end RothschildStein.P2
