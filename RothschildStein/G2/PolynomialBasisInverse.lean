-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OppositeGroup
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The polynomial coefficient matrix of the canonical basis
(BB Lemma 11.21, p. 552; polynomial basis inversion). -/
def canonicalCoefficientMatrix : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℝ) :=
  leftCoefficient G

/-- The canonical coefficient matrix is upper triangular (BB Theorem 3.29, p. 110). -/
theorem canonicalCoefficientMatrix_upper : (canonicalCoefficientMatrix G).IsUpperTriangular := by
  intro i k hki
  rw [canonicalCoefficientMatrix, leftCoefficient_of_le G i k (le_of_lt hki)]
  simp only [ite_eq_right (show i ≠ k by intro h; subst k; exact lt_irrefl _ hki)]

/-- Its determinant is one (BB Theorem 3.29, p. 110). -/
theorem canonicalCoefficientMatrix_det : (canonicalCoefficientMatrix G).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (canonicalCoefficientMatrix_upper G)]
  simp [canonicalCoefficientMatrix, leftCoefficient_of_le G _ _ le_rfl]

/-- The inverse coefficient matrix is polynomial: the determinant-one adjugate
(BB Lemma 11.21, p. 552). -/
def inverseCanonicalMatrix : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℝ) :=
  (canonicalCoefficientMatrix G).adjugate

/-- The polynomial left inverse identity (BB Lemma 11.21, p. 552). -/
theorem inverseCanonicalMatrix_mul :
    inverseCanonicalMatrix G * canonicalCoefficientMatrix G = 1 := by
  rw [inverseCanonicalMatrix, Matrix.adjugate_mul, canonicalCoefficientMatrix_det, one_smul]

/-- Coordinate directions expand in the invariant basis with polynomial coefficients
(BB Lemma 11.21, p. 552). -/
theorem coordinate_basis_expansion (k : Fin N) (x : Fin N → ℝ) :
    Hormander.Interface.basisVec k =
      ∑ i, eval x (inverseCanonicalMatrix G k i) • G.canonicalField i x := by
  ext j
  have h := congrArg (fun M => eval x (M k j)) (inverseCanonicalMatrix_mul G)
  simpa [Matrix.mul_apply, canonicalCoefficientMatrix, canonicalField_coordinate,
    Hormander.Interface.basisVec, Pi.single_apply, Matrix.one_apply, eq_comm] using h.symm

end RothschildStein.G2
