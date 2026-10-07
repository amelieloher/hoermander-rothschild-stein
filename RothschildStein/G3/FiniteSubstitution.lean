-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialEvaluation
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The error in multiplying canonical representatives is invisible
through the cutoff (BB (9.75), p. 468). -/
theorem finitePolynomial_product_error {a s : ℕ}
    (f g : WordCoefficients a s (fun _ => 1)) :
    ordinaryTrunc s (polynomialSeries a
      (finitePolynomial (truncatedProduct f g) - finitePolynomial f * finitePolynomial g)) = 0 := by
  have hfg := truncateSeries_finitePolynomial
    (truncatedProduct f g : FiniteWordAlgebra a s (fun _ => 1))
  have hf := truncateSeries_finitePolynomial (f : FiniteWordAlgebra a s (fun _ => 1))
  have hg := truncateSeries_finitePolynomial (g : FiniteWordAlgebra a s (fun _ => 1))
  change truncateSeries (polynomialSeries a
    (finitePolynomial (truncatedProduct f g) - finitePolynomial f * finitePolynomial g)) = 0
  simp only [map_sub, map_mul]
  rw [hfg, hf, hg]
  exact sub_self _

/-- Positive-order polynomial evaluation respects the truncated coefficient
product (BB (9.75), p. 468). -/
theorem finiteSubstitution_mul {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (f g : WordCoefficients a s (fun _ => 1)) :
    polynomialEvaluation X (finitePolynomial (truncatedProduct f g)) =
      polynomialEvaluation X (finitePolynomial f) * polynomialEvaluation X (finitePolynomial g) := by
  have h := polynomialEvaluation_eq_zero_of_truncate_zero X hX _ (finitePolynomial_product_error f g)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

/-- Safe substitution of arbitrary positive-order elements into the finite
ordinary-degree coefficient quotient (BB (9.75), p. 468). -/
def finiteSubstitutionHom {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) :
    FiniteWordAlgebra a s (fun _ => 1) →ₐ[ℝ] FiniteWordAlgebra b s p where
  toFun f := polynomialEvaluation X (finitePolynomial f)
  map_one' := (congrArg (polynomialEvaluation X) finitePolynomial_unit).trans (map_one _)
  map_zero' := (congrArg (polynomialEvaluation X) finitePolynomial_zero).trans (map_zero _)
  map_mul' := finiteSubstitution_mul X hX
  map_add' f g :=
    (congrArg (polynomialEvaluation X)
      (finitePolynomial_add (f : WordCoefficients a s (fun _ => 1)) g)).trans (map_add _ _ _)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    have h := congrArg (polynomialEvaluation X)
      (finitePolynomial_smul r (truncatedUnit : WordCoefficients a s (fun _ => 1)))
    rw [map_smul, finitePolynomial_unit, map_one] at h
    exact h

/-- Finite substitution preserves every lower-order filtration level
(BB p. 468). -/
theorem finiteSubstitutionHom_order {a b s k : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    {f : FiniteWordAlgebra a s (fun _ => 1)} (hf : FiniteOrderAtLeast k f) :
    FiniteOrderAtLeast k (finiteSubstitutionHom X hX f) := by
  apply polynomialEvaluation_order X hX
  have h := polynomialSeries_finitePolynomial (f : WordCoefficients a s (fun _ => 1))
  rw [h]
  exact hf
end RothschildStein.G3
