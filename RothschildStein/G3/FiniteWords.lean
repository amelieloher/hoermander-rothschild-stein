-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.Definitions.WordCoefficients
public import RothschildStein.Definitions.boundedWordList
public import RothschildStein.Definitions.truncatedBracket
public import RothschildStein.Definitions.formalSpan
public import RothschildStein.Definitions.freeDimension
public import RothschildStein.Definitions.FormalRelation
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Word weights add under concatenation (BB Proposition 10.42, p. 523). -/
@[simp] theorem weight_append {a : ℕ} (p : Fin a → ℕ+) (I J : List (Fin a)) :
    wordWeight p (I ++ J) = wordWeight p I + wordWeight p J := by
  simp [wordWeight]

/-- Positive letter weights bound ordinary length (BB Proposition 10.44, p. 525). -/
theorem length_le_weight {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) :
    I.length ≤ wordWeight p I := by
  induction I with
  | nil => simp [wordWeight]
  | cons i I ih =>
    have hi := (p i).pos
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- The fixed word family contains exactly the words through weighted order s
(BB Proposition 10.44, pp. 524–525). -/
theorem mem_wordFamily_iff {a s : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) :
    I ∈ wordFamily p s ↔ wordWeight p I ≤ s := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨I.length, Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.lt_succ_of_le ((length_le_weight p I).trans h)
    · exact Finset.mem_image.mpr ⟨I.get, Finset.mem_univ _, List.ofFn_get I⟩

/-- A prefix never has greater weight than its word (BB Proposition 10.42, p. 523). -/
theorem weight_take_le {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) (r : ℕ) :
    wordWeight p (I.take r) ≤ wordWeight p I := by
  have h := weight_append p (I.take r) (I.drop r)
  rw [List.take_append_drop] at h
  omega

/-- A suffix never has greater weight than its word (BB Proposition 10.42, p. 523). -/
theorem weight_drop_le {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a)) (r : ℕ) :
    wordWeight p (I.drop r) ≤ wordWeight p I := by
  have h := weight_append p (I.take r) (I.drop r)
  rw [List.take_append_drop] at h
  omega

/-- Canonical inclusion of a word with its weighted-cutoff proof (BB pp. 524–525). -/
def boundedWord {a s : ℕ} (p : Fin a → ℕ+) (I : List (Fin a))
    (h : wordWeight p I ≤ s) : BoundedWord a s p :=
  ⟨I, (mem_wordFamily_iff p I).mpr h⟩

/-- The bounded-word inclusion preserves the actual word (BB p. 525). -/
@[simp] theorem boundedWord_list {a s : ℕ} (p : Fin a → ℕ+) (I : List (Fin a))
    (h : wordWeight p I ≤ s) : boundedWordList (boundedWord p I h) = I := rfl

/-- A bounded word satisfies its asserted weight cutoff (BB p. 525). -/
theorem boundedWord_weight {a s : ℕ} {p : Fin a → ℕ+} (I : BoundedWord a s p) :
    wordWeight p (boundedWordList I) ≤ s :=
  (mem_wordFamily_iff p I.val).mp I.property

/-- Universal relations in the finite model are exactly the coefficientwise
relations, with every associative word retained (BB (10.52), pp. 524–527). -/
theorem formalRelation_iff_coefficients {a s : ℕ} {p : Fin a → ℕ+}
    (c : BoundedWord a s p → ℝ) : FormalRelation c ↔
      ∀ J : BoundedWord a s p,
        (∑ I, c I * formalBracket (boundedWordList I) (boundedWordList J)) = 0 := by
  simp only [FormalRelation]
  constructor
  · intro h J
    have he := congrFun h J
    simpa [truncatedBracket, Finset.sum_apply] using he
  · intro h
    funext J
    simpa [truncatedBracket, Finset.sum_apply] using h J

/-- Every bounded nonempty formal commutator belongs to the fixed formal span
(BB Definition 10.43 and Remark 10.46, pp. 524–525). -/
theorem truncatedBracket_mem_span {a s : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s) :
    truncatedBracket I ∈ formalSpan a s p :=
  Submodule.subset_span ⟨I, hne, hI, rfl⟩

end RothschildStein.G3
