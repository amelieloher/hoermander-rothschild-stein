-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- A matrix acting on the sup-norm coordinate space
(BB Prop 9.50, p. 445). -/
def matrixOperator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.mulVecLin M).toContinuousLinearMap

/-- An entry bound κ gives the dimension-times-κ sup operator bound,
including the zero-dimensional case (BB Prop 9.50, p. 445). -/
theorem matrixOperator_norm_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : ∀ i j, |M i j| ≤ κ) :
    ‖matrixOperator M‖ ≤ n * κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (n : ℝ) * κ * ‖u‖)).mpr
  intro i
  change ‖∑ j, M i j * u j‖ ≤ (n : ℝ) * κ * ‖u‖
  calc
    ‖∑ j, M i j * u j‖ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, κ * ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hM i j) (norm_le_pi_norm u j) (norm_nonneg _) hκ
    _ = (n : ℝ) * κ * ‖u‖ := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]; ring

/-- The weighted entry estimate cancels exactly under diagonal
normalization, with row/output weight first and column/input weight second
(BB Lemmas 9.49/9.51, pp. 443–447). -/
theorem weightedMatrix_entry_bound {n : ℕ} (w : Fin n → ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) {r κ : ℝ} (hr : 0 < r)
    (hM : ∀ i j, |M i j| ≤ κ * r ^ w i / r ^ w j) :
    ∀ i j, |M i j * r ^ w j / r ^ w i| ≤ κ := by
  intro i j
  rw [abs_div, abs_mul, abs_of_pos (pow_pos hr (w j)), abs_of_pos (pow_pos hr (w i))]
  apply (div_le_iff₀ (pow_pos hr (w i))).mpr
  have h := mul_le_mul_of_nonneg_right (hM i j) (pow_nonneg hr.le (w j))
  rwa [div_mul_cancel₀ _ (ne_of_gt (pow_pos hr (w j)))] at h

end RothschildStein.G4
