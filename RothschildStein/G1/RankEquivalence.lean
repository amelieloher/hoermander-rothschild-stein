-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.WeightedNormalization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C

namespace RothschildStein.G1

/-- Every nonempty standard word has a right-nested tree (BB Def 1.17, p. 10). -/
theorem exists_nestedWord_of_list {k : ℕ} (I : List (Fin (k + 1))) (hne : I ≠ []) :
    ∃ u : NestedWord k, nestedLetters u = I := by
  induction I with
  | nil => exact False.elim (hne rfl)
  | cons i I ih =>
      cases I with
      | nil => exact ⟨.generator i, rfl⟩
      | cons j I =>
          obtain ⟨u, hu⟩ := ih (by simp)
          exact ⟨.bracket i u, by simp [nestedLetters, hu]⟩

/-- Embedding of a standard word in the binary bracket carrier (BB pp. 10–12). -/
def nestedToBinary {k : ℕ} : NestedWord k → Hormander.Interface.LieWord k
  | .generator i => .generator i
  | .bracket i u => .bracket (.generator i) (nestedToBinary u)

/-- The embedding retains actual field evaluation (BB pp. 10–12). -/
theorem nestedToBinary_eval {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (u : NestedWord k) :
    Hormander.lieWordEval X (nestedToBinary u) = nestedEval X u := by
  induction u with
  | generator i => rfl
  | bracket i u ih => simp [nestedToBinary, Hormander.lieWordEval, nestedEval, ih]

/-- The embedding retains the assigned weighted grading (BB Lemma 1.21, p. 12). -/
theorem nestedToBinary_weight {k : ℕ} (w : Fin (k + 1) → ℕ+) (u : NestedWord k) :
    binaryWeight w (nestedToBinary u) = wordWeight w (nestedLetters u) := by
  induction u with
  | generator i => simp [nestedToBinary, binaryWeight, nestedLetters, wordWeight]
  | bracket i u ih => simp [nestedToBinary, binaryWeight, nestedLetters, wordWeight, ih]

private theorem combination_mem_span {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (c : WordCombination k) :
    combinationEval X c x ∈ Submodule.span ℝ
      {v | ∃ I : List (Fin (k + 1)), I ≠ [] ∧ v = wordBracket X I x} := by
  induction c with
  | nil => exact Submodule.zero_mem _
  | cons z c ih =>
      rcases z with ⟨a, u⟩
      apply Submodule.add_mem _ _ ih
      apply Submodule.smul_mem _ (a : ℝ)
      apply Submodule.subset_span
      exact ⟨nestedLetters u, nestedLetters_ne_nil u,
        congrFun (nestedEval_eq_wordBracket X u) x⟩

/-- The pointwise span of all binary brackets equals the span of standard
nonempty words on the original open domain (BB Def 1.22, p. 12). -/
theorem binary_span_eq_word_span {k N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    Submodule.span ℝ {v | ∃ t : Hormander.Interface.LieWord k, v = Hormander.lieWordEval X t x} =
      Submodule.span ℝ {v | ∃ I : List (Fin (k + 1)), I ≠ [] ∧ v = wordBracket X I x} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨t, rfl⟩
    rw [← binaryExpansion_eqOn hΩ X hX t hx]
    exact combination_mem_span X x (binaryExpansion t)
  · apply Submodule.span_le.mpr
    rintro v ⟨I, hne, rfl⟩
    obtain ⟨u, hu⟩ := exists_nestedWord_of_list I hne
    apply Submodule.subset_span
    refine ⟨nestedToBinary u, ?_⟩
    rw [nestedToBinary_eval, nestedEval_eq_wordBracket, hu]

end RothschildStein.G1
