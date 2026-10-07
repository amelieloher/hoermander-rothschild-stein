-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordPolynomials
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The canonical finite polynomial representative is linear in its
coefficient carrier (BB Lemma 9.22, pp. 413–414). -/
def finitePolynomialLinear {a s : ℕ} {p : Fin a → ℕ+} :
    WordCoefficients a s p →ₗ[ℝ] MonoidAlgebra ℝ (FreeMonoid (Fin a)) where
  toFun := finitePolynomial
  map_add' := finitePolynomial_add
  map_smul' := finitePolynomial_smul
end RothschildStein.G3
