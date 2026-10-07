-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BasisExponentialEvaluation
public import RothschildStein.G3.LinearFieldEvaluation
public import RothschildStein.G3.FiniteLieFields
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- The bracket-basis input has exactly the untruncated linear
word polynomial with its basis coefficients. -/
theorem finitePolynomial_basisCoefficientInput {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    finitePolynomial (basisCoefficientInput D f) = linearWordPolynomial (D.basis.equivFun f) := by
  change finitePolynomial (∑ j, D.basis.equivFun f j •
    (truncatedBracket [j] : WordCoefficients (freeDimension a s p) s (basisAlphabetWeight D))) = _
  exact finitePolynomial_linear_input (fun j => D.weight_bound j) _

/-- Truncating the untruncated linear basis polynomial recovers
its finite coefficient input. -/
theorem truncate_linear_basis_input {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    truncateSeries (s := s) (p := basisAlphabetWeight D)
      (polynomialSeries (freeDimension a s p) (linearWordPolynomial (D.basis.equivFun f))) =
      basisCoefficientInput D f := by
  rw [← finitePolynomial_basisCoefficientInput, truncateSeries_finitePolynomial]

end RothschildStein.G3
