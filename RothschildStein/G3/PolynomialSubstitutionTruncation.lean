-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialSubstitutionHomogeneity
public import RothschildStein.G3.PolynomialEvaluation
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted truncation commutes with untruncated associative
polynomial substitution (BB Lemma 9.22). -/
theorem truncate_associativeWordSubstitution {a b s : ℕ} {p : Fin b → ℕ+}
    (A : Fin a → MonoidAlgebra ℝ (FreeMonoid (Fin b)))
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a))) :
    truncateSeries (s := s) (p := p)
      (polynomialSeries b (associativeWordSubstitution A P)) =
      polynomialEvaluation
        (fun i => truncateSeries (s := s) (p := p) (polynomialSeries b (A i))) P := by
  have h := associativeWordSubstitution_evaluation A
    ((truncateSeries (s := s) (p := p)).comp (polynomialSeries b))
  exact congrArg (fun F => F P) h

/-- With weight-homogeneous substitutions, canonical polynomial
representatives commute with substitution exactly, since no coefficient
exceeds the cutoff (BB Lemma 9.22, pp. 413–414). -/
theorem finitePolynomial_associativeWordSubstitution {a b s : ℕ}
    (q : Fin a → ℕ+) (p : Fin b → ℕ+)
    (A : Fin a → MonoidAlgebra ℝ (FreeMonoid (Fin b)))
    (hA : ∀ i, Homogeneous p (q i) (polynomialSeries b (A i)))
    (f : WordCoefficients a s q) :
    let g : WordCoefficients b s p := polynomialEvaluation
      (fun i => truncateSeries (s := s) (p := p) (polynomialSeries b (A i)))
      (finitePolynomial f)
    finitePolynomial g = associativeWordSubstitution A (finitePolynomial f) := by
  have ht := truncate_associativeWordSubstitution (s := s) (p := p) A (finitePolynomial f)
  let g : WordCoefficients b s p := restrict
    (polynomialSeries b (associativeWordSubstitution A (finitePolynomial f)))
  have he : finitePolynomial g = associativeWordSubstitution A (finitePolynomial f) :=
    finitePolynomial_restrict_polynomial_exact _
      (associativeWordSubstitution_finitePolynomial_weight_bound q p A hA f)
  change (g : FiniteWordAlgebra b s p) = _ at ht
  rw [← ht]
  exact he
end RothschildStein.G3
