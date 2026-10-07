-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BracketAlphabetEvaluation
public import RothschildStein.G3.PolynomialSubstitutionTruncation
public import RothschildStein.G3.BasisAlphabetSubstitution
public import RothschildStein.G3.BracketPolynomialCoefficients
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- A weight-preserving finite substitution by bracket words agrees
exactly with actual differential evaluation in the bracket alphabet. The
source cutoff prevents any lost primitive terms (BB Lemma 9.22). -/
theorem differentialWordEvaluation_finiteBracketAlphabet {a b s N : ℕ}
    {p : Fin b → ℕ+} (q : Fin a → ℕ+)
    (Ω : Opens (Fin N → ℝ))
    (X : Fin b → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : Fin a → List (Fin b)) (hne : ∀ i, I i ≠ [])
    (hw : ∀ i, wordWeight p (I i) = (q i : ℕ))
    (f : FiniteWordAlgebra a s q) :
    differentialWordEvaluation Ω X hX
      (finitePolynomial (weightedFiniteSubstitutionHom q
        (fun i => finiteBracketWord (s := s) (p := p) (I i))
        (fun i => by rw [← hw i]; exact finiteBracketWord_weight_order (s := s) p (I i)) f)) =
      differentialWordEvaluation Ω (fun i => wordBracket X (I i))
        (fun i => G1.wordBracket_contDiffOn Ω.isOpen X hX (I i)) (finitePolynomial f) := by
  let A := fun i => bracketWordPolynomial (I i)
  have hA : ∀ i, Homogeneous p (q i) (polynomialSeries b (A i)) := by
    intro i
    rw [polynomialSeries_bracketWord, ← hw i]
    exact formalBracket_homogeneous p (I i)
  have ht : ∀ i, truncateSeries (s := s) (p := p) (polynomialSeries b (A i)) =
      finiteBracketWord (I i) := by
    intro i
    rw [polynomialSeries_bracketWord]
    rfl
  let g : WordCoefficients a s q := f
  have he := finitePolynomial_associativeWordSubstitution q p A hA g
  dsimp only at he
  simp_rw [ht] at he
  change finitePolynomial (weightedFiniteSubstitutionHom q
    (fun i => finiteBracketWord (s := s) (p := p) (I i))
    (fun i => by rw [← hw i]; exact finiteBracketWord_weight_order (s := s) p (I i)) f) =
    associativeWordSubstitution A (finitePolynomial f) at he
  rw [he]
  exact congrArg (fun F => F (finitePolynomial f))
    (differentialWordEvaluation_bracketAlphabet Ω X hX I hne)
end RothschildStein.G3
