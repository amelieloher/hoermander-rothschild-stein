-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordExponentialSupport
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Ordinary support lengths add under associative polynomial
multiplication, preserving the jet budget of two-flow Taylor products. -/
theorem polynomial_product_length_bound {a m n : ℕ}
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : ∀ I, m < I.length → polynomialSeries a P I = 0)
    (hQ : ∀ I, n < I.length → polynomialSeries a Q I = 0)
    (I : List (Fin a)) (hI : m + n < I.length) :
    polynomialSeries a (P * Q) I = 0 := by
  rw [map_mul]
  change wordConvolution (polynomialSeries a P) (polynomialSeries a Q) I = 0
  unfold wordConvolution
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : m < (I.take k).length
  · rw [hP _ hk, zero_mul]
  · have hl : n < (I.drop k).length := by
      have hh := congrArg List.length (List.take_append_drop k I)
      rw [List.length_append] at hh
      omega
    rw [hQ _ hl, mul_zero]

/-- A rectangular pair of degree-s exponential Taylor polynomials
uses at most 2s ordinary primitive factors (BB (9.10), p. 411). -/
theorem wordPolynomialExp_product_length_bound {a s : ℕ}
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hP : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a P))
    (hQ : Homogeneous (fun _ : Fin a => 1) 1 (polynomialSeries a Q))
    (I : List (Fin a)) (hI : 2 * s < I.length) :
    polynomialSeries a (wordPolynomialExp P s * wordPolynomialExp Q s) I = 0 := by
  apply polynomial_product_length_bound _ _
    (wordPolynomialExp_coeff_eq_zero_of_length_gt P hP)
    (wordPolynomialExp_coeff_eq_zero_of_length_gt Q hQ) I
  omega
end RothschildStein.G3
