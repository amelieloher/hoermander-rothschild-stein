-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.PolynomialBasisInverse
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
variable {N : ℕ} (G : HomogeneousGroup N)

private def evalMatrix (x : Fin N → ℝ)
    (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℝ)) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => eval x (M i j)

private theorem evalMatrix_inverse (x : Fin N → ℝ) :
    evalMatrix x (inverseCanonicalMatrix G) = (evalMatrix x (canonicalCoefficientMatrix G))⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  ext i j
  have h := congrArg (fun M => eval x (M i j)) (inverseCanonicalMatrix_mul G)
  simpa [evalMatrix, Matrix.mul_apply, Matrix.one_apply] using h

private def weightDiagonal (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => t ^ (G.weight i : ℝ)

private theorem weightDiagonal_inv (t : ℝ) (ht : 0 < t) :
    (weightDiagonal G t)⁻¹ = Matrix.diagonal (fun i => t ^ (-(G.weight i : ℝ))) := by
  apply Matrix.inv_eq_left_inv
  rw [weightDiagonal, Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin N => t ^ (-(G.weight i : ℝ)) * t ^ (G.weight i : ℝ)) =
      fun _ => (1 : ℝ) := by
    funext i
    rw [Real.rpow_neg ht.le]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht _))
  simp only [h, Matrix.diagonal_one]

private theorem coefficientMatrix_conjugate (t : ℝ) (ht : 0 < t) (x : Fin N → ℝ) :
    evalMatrix (G.dilate t x) (canonicalCoefficientMatrix G) =
      (weightDiagonal G t)⁻¹ * evalMatrix x (canonicalCoefficientMatrix G) * weightDiagonal G t := by
  ext i j
  rw [weightDiagonal_inv G t ht]
  simp only [weightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, evalMatrix,
    canonicalCoefficientMatrix, leftCoefficient_eval_dilate G i j t ht x]
  rw [show (G.weight j : ℝ) - G.weight i = -(G.weight i : ℝ) + G.weight j by ring,
    Real.rpow_add ht]
  ring

/-- The polynomial inverse matrix has the same difference-of-weights rule
(BB Lemma 11.21, p. 552). -/
theorem inverseCanonicalMatrix_eval_dilate (i j : Fin N) (t : ℝ) (ht : 0 < t)
    (x : Fin N → ℝ) :
    eval (G.dilate t x) (inverseCanonicalMatrix G i j) =
      t ^ ((G.weight j : ℝ) - G.weight i) * eval x (inverseCanonicalMatrix G i j) := by
  have hdet : IsUnit (weightDiagonal G t).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [weightDiagonal, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (Real.rpow_pos_of_pos ht _)
  have h : evalMatrix (G.dilate t x) (inverseCanonicalMatrix G) =
      (weightDiagonal G t)⁻¹ * evalMatrix x (inverseCanonicalMatrix G) * weightDiagonal G t := by
    rw [evalMatrix_inverse G, coefficientMatrix_conjugate G t ht x,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet, ← evalMatrix_inverse G]
    rw [Matrix.mul_assoc]
  have hc := congrArg (fun M => M i j) h
  rw [weightDiagonal_inv G t ht] at hc
  simp only [weightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, evalMatrix] at hc
  rw [show (G.weight j : ℝ) - G.weight i = -(G.weight i : ℝ) + G.weight j by ring,
    Real.rpow_add ht]
  rw [hc]
  ring

end RothschildStein.G2
