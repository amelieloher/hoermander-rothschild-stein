-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialProductSupport
public import RothschildStein.G3.ExponentialPolynomialRemainder
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A two-flow exponential product agrees through the cutoff with
the finite BCH exponential (BB Lemma 9.22, pp. 413–414). -/
theorem exponentialProduct_remainder_truncate_zero {a s : ℕ} {p : Fin a → ℕ+}
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a P)))
    (hQ : FiniteOrderAtLeast 1 (truncateSeries (s := s) (p := p) (polynomialSeries a Q))) :
    truncateSeries (s := s) (p := p) (polynomialSeries a
      (wordPolynomialExp P s * wordPolynomialExp Q s -
        finitePolynomial (finiteExp (finiteBCH
          (truncateSeries (s := s) (p := p) (polynomialSeries a P))
          (truncateSeries (s := s) (p := p) (polynomialSeries a Q)))))) = 0 := by
  rw [map_sub, map_sub, map_mul, map_mul, truncate_wordPolynomialExp P hP,
    truncate_wordPolynomialExp Q hQ, truncateSeries_finitePolynomial, finiteExp_BCH hP hQ,
    sub_self]

/-- The discarded two-flow/BCH exponential product tail uses at
most 2s ordinary factors, independently of weighted cutoff bookkeeping. -/
theorem exponentialProduct_remainder_length_bound {a s : ℕ} {p : Fin a → ℕ+}
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P))
    (hQ : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a Q))
    (I : List (Fin a)) (hI : 2 * s < I.length) :
    polynomialSeries a (wordPolynomialExp P s * wordPolynomialExp Q s -
      finitePolynomial (finiteExp (finiteBCH
        (truncateSeries (s := s) (p := p) (polynomialSeries a P))
        (truncateSeries (s := s) (p := p) (polynomialSeries a Q))))) I = 0 := by
  let A : WordCoefficients a s p := finiteExp (finiteBCH
    (truncateSeries (s := s) (p := p) (polynomialSeries a P))
    (truncateSeries (s := s) (p := p) (polynomialSeries a Q)))
  rw [map_sub]
  change polynomialSeries a (wordPolynomialExp P s * wordPolynomialExp Q s) I -
    polynomialSeries a (finitePolynomial A) I = 0
  rw [wordPolynomialExp_product_length_bound P Q hP hQ I hI,
    finitePolynomial_coeff_zero_of_length_gt A I (by omega), sub_self]
end RothschildStein.G3
