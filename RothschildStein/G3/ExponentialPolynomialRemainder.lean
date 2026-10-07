-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordExponentialSupport
public import RothschildStein.G3.PolynomialSupportLengthBounds
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The ordinary exponential Taylor polynomial and its weighted
finite exponential agree through the weighted cutoff (BB pp. 413–414). -/
theorem exponentialPolynomial_remainder_truncate_zero {a s : ℕ}
    {p : Fin a → ℕ+} (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a P))) :
    truncateSeries (s := s) (p := p) (polynomialSeries a
      (wordPolynomialExp P s - finitePolynomial
        (finiteExp (truncateSeries (s := s) (p := p) (polynomialSeries a P))))) = 0 := by
  rw [map_sub, map_sub, truncate_wordPolynomialExp P hP,
    truncateSeries_finitePolynomial, sub_self]

/-- Every polynomial invisible in the cutoff-s quotient has zero
coefficients on all words of weight at most s (BB Lemma 9.22). -/
theorem polynomial_coeff_zero_of_truncate_zero {a s : ℕ} {p : Fin a → ℕ+}
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : truncateSeries (s := s) (p := p) (polynomialSeries a P) = 0)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    polynomialSeries a P I = 0 := by
  have hh := congrArg (fun f : FiniteWordAlgebra a s p => f (boundedWord p I hI)) hP
  exact hh

/-- Canonical cutoff-s representatives use at most s ordinary
operator factors, because every letter has positive weight. -/
theorem finitePolynomial_coeff_zero_of_length_gt {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) (I : List (Fin a)) (hI : s < I.length) :
    polynomialSeries a (finitePolynomial f) I = 0 := by
  rw [polynomialSeries_finitePolynomial]
  have hw : ¬wordWeight p I ≤ s := by have hh := length_le_weight p I; omega
  simp only [extend, dite_eq_right hw]

/-- The discarded weighted exponential tail retains ordinary
operator length at most s, preserving the bracket-field jet budget. -/
theorem exponentialPolynomial_remainder_length_bound {a s : ℕ} {p : Fin a → ℕ+}
    (P : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P))
    (I : List (Fin a)) (hI : s < I.length) :
    polynomialSeries a (wordPolynomialExp P s - finitePolynomial
      (finiteExp (truncateSeries (s := s) (p := p) (polynomialSeries a P)))) I = 0 := by
  rw [map_sub]
  change polynomialSeries a (wordPolynomialExp P s) I -
    polynomialSeries a (finitePolynomial _) I = 0
  let f : WordCoefficients a s p := finiteExp (truncateSeries (s := s) (p := p) (polynomialSeries a P))
  change polynomialSeries a (wordPolynomialExp P s) I - polynomialSeries a (finitePolynomial f) I = 0
  rw [wordPolynomialExp_coeff_eq_zero_of_length_gt P hP I hI,
    finitePolynomial_coeff_zero_of_length_gt f I hI, sub_self]
end RothschildStein.G3
