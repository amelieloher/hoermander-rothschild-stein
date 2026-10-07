-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelLieBracket
public import RothschildStein.G3.FieldCoordinates
public import RothschildStein.Definitions.FreeAt
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Every commutator word, including the zero empty word, belongs
to the fixed finite span (BB pp. 524–525). -/
theorem truncatedBracket_mem_formalSpan {a s : ℕ} {p : Fin a → ℕ+} (I : List (Fin a)) :
    (truncatedBracket I : WordCoefficients a s p) ∈ formalSpan a s p := by
  by_cases he : I = []
  · subst I
    have hz : (truncatedBracket [] : WordCoefficients a s p) = 0 := rfl
    rw [hz]
    exact Submodule.zero_mem _
  · by_cases hw : wordWeight p I ≤ s
    · exact truncatedBracket_mem_span I he hw
    · rw [truncatedBracket_eq_zero_of_weight_gt I (by omega)]
      exact Submodule.zero_mem _

/-- A finite commutator as an element of the fixed Lie carrier
(BB Proposition 10.54, p. 531). -/
def wordLieElement {a s : ℕ} {p : Fin a → ℕ+} (I : List (Fin a)) : formalSpan a s p :=
  ⟨truncatedBracket I, truncatedBracket_mem_formalSpan I⟩

/-- Coordinates of a commutator word (BB (10.57), p. 531). -/
def wordCoordinates {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (I : List (Fin a)) : Fin M → ℝ :=
  e.symm (wordLieElement I)

/-- The empty word has zero coordinates (BB p. 531). -/
@[simp] theorem wordCoordinates_nil {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) : wordCoordinates e [] = 0 := by
  have hz : wordLieElement (a := a) (s := s) (p := p) [] = 0 := Subtype.ext rfl
  rw [wordCoordinates, hz, map_zero]

/-- Nested coefficient commutators agree with word concatenation
(BB (10.57), p. 531). -/
theorem coefficient_nested_cons {a s : ℕ} {p : Fin a → ℕ+}
    (i j : Fin a) (I : List (Fin a)) :
    ⁅finiteLetter (s := s) (p := p) i, finiteBracketWord (s := s) (p := p) (j :: I)⁆ = finiteBracketWord (s := s) (p := p) (i :: j :: I) := by
  obtain ⟨u, hu⟩ := exists_nested_of_list (j :: I) (by simp)
  have h := nested_eval_truncatedBracket (s := s) (p := p) (Nested.bracket i u)
  simpa only [Nested.eval, Nested.letters, nested_eval_truncatedBracket, hu, finiteBracketWord] using h

/-- The coordinate Lie bracket agrees with nested word coefficients
(BB (10.57), p. 531). -/
theorem wordCoordinates_cons {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (i j : Fin a) (I : List (Fin a)) :
    coordinateLieBracket e (wordCoordinates e [i]) (wordCoordinates e (j :: I)) =
      wordCoordinates e (i :: j :: I) := by
  have hInj : Function.Injective (coordinateInclusionCL e) :=
    fun u v h => e.injective (Subtype.ext h)
  apply hInj
  rw [coordinateInclusionCL_lieBracket]
  have hi : coordinateInclusionCL e (wordCoordinates e [i]) = finiteLetter i :=
    congrArg Subtype.val (e.apply_symm_apply (wordLieElement [i]))
  have hJ : coordinateInclusionCL e (wordCoordinates e (j :: I)) = finiteBracketWord (j :: I) :=
    congrArg Subtype.val (e.apply_symm_apply (wordLieElement (j :: I)))
  have hIJ : coordinateInclusionCL e (wordCoordinates e (i :: j :: I)) = finiteBracketWord (i :: j :: I) :=
    congrArg Subtype.val (e.apply_symm_apply (wordLieElement (i :: j :: I)))
  rw [hi, hJ, hIJ, coefficient_nested_cons]

/-- The original model generator fields (BB Theorems 10.31–10.32). -/
def modelGenerators {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) : Fin a → (Fin M → ℝ) → Fin M → ℝ :=
  fun i => modelField e (wordCoordinates e [i])

/-- Fixed nested word brackets are precisely the invariant model
fields associated to their formal coefficients (BB (10.57), p. 531). -/
theorem wordBracket_modelGenerators {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (I : List (Fin a)) :
    wordBracket (modelGenerators e) I = modelField e (wordCoordinates e I) := by
  induction I with
  | nil =>
    funext u
    simp only [wordBracket, wordCoordinates_nil, modelField, map_zero, Pi.zero_apply]
  | cons i I ih =>
    cases I with
    | nil => rfl
    | cons j I =>
      change VectorField.lieBracket ℝ (modelField e (wordCoordinates e [i]))
        (wordBracket (modelGenerators e) (j :: I)) = _
      rw [ih]
      funext u
      rw [modelField_lieBracket, wordCoordinates_cons]
end RothschildStein.G3
