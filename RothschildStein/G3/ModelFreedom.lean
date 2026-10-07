-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelWords
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Formal coefficients are transported isomorphically to model fields
at any point (BB Proposition 10.54, p. 530). -/
def coefficientFieldEquiv {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    formalSpan a s p ≃ₗ[ℝ] (Fin M → ℝ) :=
  e.symm.trans (modelFieldAtEquiv e u)

/-- Coefficient-to-field transport agrees with each fixed word bracket
(BB (10.57), p. 531). -/
theorem coefficientFieldEquiv_word {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) (I : List (Fin a)) :
    coefficientFieldEquiv e u (wordLieElement I) = wordBracket (modelGenerators e) I u := by
  rw [wordBracket_modelGenerators]
  rfl

/-- Fixed coefficient relations are exactly zero sums in the finite
Lie carrier (BB equations (10.50)–(10.52), pp. 525–526). -/
theorem formalRelation_iff_wordLieElement_sum_zero {a s : ℕ} {p : Fin a → ℕ+}
    (c : BoundedWord a s p → ℝ) :
    FormalRelation c ↔ (∑ I, c I • wordLieElement (boundedWordList I) : formalSpan a s p) = 0 := by
  have he : (formalSpan a s p).subtype (∑ I, c I • wordLieElement (boundedWordList I)) =
      ∑ I, c I • (truncatedBracket (boundedWordList I) : WordCoefficients a s p) := by
    rw [map_sum]
    simp only [map_smul, Submodule.subtype_apply, wordLieElement]
  constructor
  · intro h
    apply (formalSpan a s p).subtype_injective
    rw [he, map_zero]
    exact h
  · intro h
    change (∑ I, c I • (truncatedBracket (boundedWordList I) : WordCoefficients a s p)) = 0
    rw [← he, h, map_zero]

/-- Model generators are free up to the specified weighted step at
every point, in the exact fixed coefficient-relation sense
(BB Proposition 10.54 and Theorems 10.31–10.32, pp. 511–512, 531). -/
theorem freeAt_modelGenerators {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    FreeAt p s (modelGenerators e) u := by
  intro c
  rw [formalRelation_iff_wordLieElement_sum_zero]
  have he : (∑ I, c I • wordBracket (modelGenerators e) (boundedWordList I) u) =
      coefficientFieldEquiv e u (∑ I, c I • wordLieElement (boundedWordList I)) := by
    rw [map_sum]
    simp only [map_smul, coefficientFieldEquiv_word]
  rw [he]
  exact (coefficientFieldEquiv e u).map_eq_zero_iff
end RothschildStein.G3
