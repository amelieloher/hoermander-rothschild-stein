-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialBracketEvaluation
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The untruncated associative commutator polynomial has exactly
the fixed formal bracket coefficients (BB Lemma 9.22, pp. 413–414). -/
theorem polynomialSeries_bracketWord {a : ℕ} (I : List (Fin a)) :
    polynomialSeries a (bracketWordPolynomial I) = (formalBracket I : CoefficientSeries a) := by
  induction I with
  | nil => rw [bracketWordPolynomial, map_zero]; rfl
  | cons i I ih =>
    cases I with
    | nil =>
      rw [bracketWordPolynomial, polynomialSeries_single, one_smul]
      rfl
    | cons j I =>
      change polynomialSeries a
        ⁅MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ), bracketWordPolynomial (j :: I)⁆ = _
      simp only [Ring.lie_def, map_sub, map_mul]
      rw [ih, polynomialSeries_single, one_smul]
      rfl

/-- For a word within the chosen weight cutoff, the canonical
polynomial representative loses no commutator coefficient (BB pp. 413–414). -/
theorem finitePolynomial_truncatedBracket {a s : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    finitePolynomial (truncatedBracket I : WordCoefficients a s p) = bracketWordPolynomial I := by
  apply polynomialSeries_injective a
  rw [polynomialSeries_finitePolynomial, polynomialSeries_bracketWord]
  funext J
  by_cases hJ : wordWeight p J ≤ s
  · simp [extend, hJ, truncatedBracket, boundedWord, boundedWordList]
  · have hz := formalBracket_homogeneous p I J (by omega)
    simp [extend, hJ, hz]

/-- Evaluation of the fixed finite formal bracket is the actual
variable-coefficient field bracket whenever its weight fits the cutoff. -/
theorem differentialWordEvaluation_truncatedBracket {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : TopologicalSpace.Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (hne : I ≠ []) (hI : wordWeight p I ≤ s) :
    differentialWordEvaluation Ω X hX
      (finitePolynomial (truncatedBracket I : WordCoefficients a s p)) =
      smoothFieldOperator Ω (wordBracket X I)
        (G1.wordBracket_contDiffOn Ω.isOpen X hX I) := by
  rw [finitePolynomial_truncatedBracket I hI]
  exact differentialWordEvaluation_bracketWord Ω X hX I hne
end RothschildStein.G3
