-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFieldJetBounds
public import RothschildStein.G3.BasisDilation
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Homogeneous basis coefficients scale by their exact weights. -/
theorem basis_equivFun_dilated {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (δ : ℝ) (f : formalSpan a s p) :
    D.basis.equivFun
      ⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩ =
        coordinateDilation D.weight δ (D.basis.equivFun f) := by
  have he : D.basis.equivFun.symm (coordinateDilation D.weight δ (D.basis.equivFun f)) =
      (⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩ : formalSpan a s p) := by
    apply Subtype.ext
    simpa only [LinearEquiv.symm_apply_apply] using
      basis_coordinateDilation D.basis D.weight D.basis_homogeneous δ (D.basis.equivFun f)
  rw [← he, LinearEquiv.apply_symm_apply]

/-- Every spatial jet of a dilated finite Lie field has a small
parameter factor, with an explicit finite word-field jet constant. -/
theorem norm_iteratedFDeriv_dilatedLieField_le {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p)
    (δ : ℝ) (hδ : |δ| ≤ 1) (r : ℕ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ r
      (finiteLieField D X ⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩) x‖ ≤
      |δ| * ∑ j, |D.basis.equivFun f j| *
        ‖iteratedFDeriv ℝ r (wordBracket X (modelBasisWord D j)) x‖ := by
  apply (norm_iteratedFDeriv_finiteLieField_le D Ω X hX _ r hx).trans
  rw [basis_equivFun_dilated, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change |δ ^ D.weight j * D.basis.equivFun f j| * _ ≤ _
  rw [abs_mul, abs_pow]
  have hp : |δ| ^ D.weight j ≤ |δ| :=
    (pow_le_pow_of_le_one (abs_nonneg δ) hδ (D.weight_pos j)).trans_eq (pow_one _)
  nlinarith [mul_le_mul_of_nonneg_right hp
    (mul_nonneg (abs_nonneg (D.basis.equivFun f j))
      (norm_nonneg (iteratedFDeriv ℝ r (wordBracket X (modelBasisWord D j)) x)))]
end RothschildStein.G3
