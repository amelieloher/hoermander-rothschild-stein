-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InverseCoefficientWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The polynomial left-to-right canonical change-of-basis matrix
(BB Lemma 11.21, p. 552; polynomial basis inversion). -/
def leftRightChangeMatrix : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℝ) :=
  canonicalCoefficientMatrix G * inverseCanonicalMatrix (oppositeGroup G)

/-- Left fields expand in the right invariant basis with polynomial coefficients
(BB Lemma 11.21, p. 552). -/
theorem canonicalField_right_expansion (i : Fin N) (x : Fin N → ℝ) :
    G.canonicalField i x = ∑ j, eval x (leftRightChangeMatrix G i j) •
      rightField G (Hormander.Interface.basisVec j) x := by
  have hm : leftRightChangeMatrix G * canonicalCoefficientMatrix (oppositeGroup G) =
      canonicalCoefficientMatrix G := by
    rw [leftRightChangeMatrix, Matrix.mul_assoc, inverseCanonicalMatrix_mul, Matrix.mul_one]
  ext k
  have h := congrArg (fun M => eval x (M i k)) hm
  simpa [Matrix.mul_apply, canonicalCoefficientMatrix, oppositeGroup_leftCoefficient,
    canonicalField_coordinate, rightField_coordinate] using h.symm

/-- Polynomial change-of-basis coefficients have the difference of weights as degree
(BB Lemma 11.21, p. 552). -/
theorem leftRightChangeMatrix_eval_dilate (i j : Fin N) (t : ℝ) (ht : 0 < t)
    (x : Fin N → ℝ) :
    eval (G.dilate t x) (leftRightChangeMatrix G i j) =
      t ^ ((G.weight j : ℝ) - G.weight i) * eval x (leftRightChangeMatrix G i j) := by
  simp only [leftRightChangeMatrix, Matrix.mul_apply, map_sum, map_mul,
    canonicalCoefficientMatrix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hopp := inverseCanonicalMatrix_eval_dilate (oppositeGroup G) k j t ht x
  rw [oppositeGroup_dilate] at hopp
  change eval (G.dilate t x) (inverseCanonicalMatrix (oppositeGroup G) k j) =
    t ^ ((G.weight j : ℝ) - G.weight k) *
      eval x (inverseCanonicalMatrix (oppositeGroup G) k j) at hopp
  rw [leftCoefficient_eval_dilate G i k t ht x, hopp]
  change (t ^ ((G.weight k : ℝ) - G.weight i) * eval x (leftCoefficient G i k)) *
    (t ^ ((G.weight j : ℝ) - G.weight k) * eval x (inverseCanonicalMatrix (oppositeGroup G) k j)) = _
  rw [show ((G.weight j : ℝ) - G.weight i) =
    ((G.weight k : ℝ) - G.weight i) + ((G.weight j : ℝ) - G.weight k) by ring,
    Real.rpow_add ht]
  ring

/-- Change-of-basis coefficients of decreasing weights vanish (BB p. 552). -/
theorem leftRightChangeMatrix_zero_of_weight_lt (i j : Fin N)
    (hij : G.weight j < G.weight i) : leftRightChangeMatrix G i j = 0 := by
  obtain hz | ⟨n, hn, _⟩ := weightedHomogeneous_of_real_eval_dilate G.weight
    (leftRightChangeMatrix G i j) ((G.weight j : ℝ) - G.weight i)
    (fun t ht x => leftRightChangeMatrix_eval_dilate G i j t ht x)
  · exact hz
  · have hc : (G.weight j : ℝ) < G.weight i := by exact_mod_cast hij
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

end RothschildStein.G2
