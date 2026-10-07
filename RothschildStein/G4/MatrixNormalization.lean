-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MatrixDeterminantSmall

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Diagonal normalization preserves the determinant. The factors
use output weight in the denominator and input weight in the numerator
(BB Lemma 9.51, pp. 446–447). -/
theorem det_weighted_normalization {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    Matrix.det (fun i j => M i j * d j / d i) = Matrix.det M := by
  have heq : (fun i j => M i j * d j / d i) =
      Matrix.of (fun i j => (d i)⁻¹ * (Matrix.of (fun k l => d l * M k l)) i j) := by
    ext i j
    simp only [Matrix.of_apply, div_eq_mul_inv]
    ring
  rw [heq, Matrix.det_mul_column, Matrix.det_mul_row]
  rw [Finset.prod_inv_distrib]
  have hp : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd i)
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- The normalization of the identity plus error is the identity
plus the normalized error (BB Lemma 9.51, pp. 446–447). -/
theorem weighted_normalization_identity_add {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (fun i j => (1 + M) i j * d j / d i) =
      (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of (fun i j => M i j * d j / d i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    field_simp [hd i]
  · simp only [Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne hij, zero_add]

end RothschildStein.G4
