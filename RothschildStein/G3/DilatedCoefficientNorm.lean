-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DilatedInputCoordinates
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Positive basis weights give a common small coefficient budget. -/
theorem norm_dilatedInputCoordinates_le {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) {δ : ℝ} (hδ : |δ| ≤ 1) :
    ‖dilatedInputCoordinates D f δ‖ ≤ |δ| * ‖D.basis.equivFun f‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg δ) (norm_nonneg _))).mpr
  intro j
  change ‖δ^D.weight j * D.basis.equivFun f j‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_pow]
  have hp : |δ|^D.weight j ≤ |δ| :=
    (pow_le_pow_of_le_one (abs_nonneg δ) hδ (D.weight_pos j)).trans_eq (pow_one _)
  exact mul_le_mul hp (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (D.basis.equivFun f) j)
    (abs_nonneg _) (abs_nonneg δ)
end RothschildStein.G3
