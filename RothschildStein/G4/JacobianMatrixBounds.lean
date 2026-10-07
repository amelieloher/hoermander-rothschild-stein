-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MatrixNormalization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- A dimension-only threshold controls the determinant of a
weighted error matrix. The diagonal powers cancel under conjugation
(BB Lemma 9.51, pp. 446–447). -/
theorem exists_weighted_determinant_threshold (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∀ (w : Fin n → ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (r : ℝ),
        0 < r → (∀ i j, |M i j| ≤ κ * r ^ w i / r ^ w j) →
          |Matrix.det (1 + M) - 1| < 1 / 2 := by
  obtain ⟨κ, hκ, hsmall, hdet⟩ := exists_matrix_perturbation_threshold n
  refine ⟨κ, hκ, hsmall, ?_⟩
  intro w M r hr hM
  let N : Matrix (Fin n) (Fin n) ℝ := fun i j => M i j * r ^ w j / r ^ w i
  have hN := weightedMatrix_entry_bound w M hr hM
  have heq : Matrix.det (1 + N) = Matrix.det (1 + M) := by
    rw [← det_weighted_normalization (1 + M) (fun i => r ^ w i)
      (fun i => ne_of_gt (pow_pos hr (w i)))]
    rw [weighted_normalization_identity_add (M := M) (d := fun i => r ^ w i)
      (fun i => ne_of_gt (pow_pos hr (w i)))]
    rfl
  rw [← heq]
  exact hdet N hN

/-- Multiplying a persistent frame by an identity-plus-error
matrix yields the stated factor-four Jacobian determinant bounds.
The factorization uses the flow-derivative expansion and frame-persistence
estimates (BB Proposition 9.50, pp. 445–446). -/
theorem jacobian_determinant_bounds_of_matrix_factorization {n : ℕ}
    (Z M J : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (hJ : J = Z * (1 + M))
    (hpersist : |lam| / 2 ≤ |Matrix.det Z| ∧ |Matrix.det Z| ≤ 2 * |lam|)
    (herror : |Matrix.det (1 + M) - 1| < 1 / 2) :
    |lam| / 4 ≤ |Matrix.det J| ∧ |Matrix.det J| ≤ 4 * |lam| := by
  have hdist := abs_lt.mp herror
  have hlo : (1 / 2 : ℝ) ≤ |Matrix.det (1 + M)| := by
    have hpos : 0 < Matrix.det (1 + M) := by linarith
    rw [abs_of_pos hpos]
    linarith
  have hhi : |Matrix.det (1 + M)| ≤ (3 / 2 : ℝ) := by
    have hpos : 0 < Matrix.det (1 + M) := by linarith
    rw [abs_of_pos hpos]
    linarith
  rw [hJ, Matrix.det_mul, abs_mul]
  constructor
  · have h := mul_le_mul hpersist.1 hlo (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _)
    nlinarith
  · have h := mul_le_mul hpersist.2 hhi (abs_nonneg _) (by positivity : 0 ≤ 2 * |lam|)
    nlinarith [abs_nonneg lam]

end RothschildStein.G4
