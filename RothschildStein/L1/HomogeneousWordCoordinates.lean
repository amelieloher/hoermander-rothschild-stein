-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFormalWordExpansion
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- A homogeneous formal Lie element has no basis coordinates in other weights. -/
theorem formal_basis_coordinate_zero_of_homogeneous {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) (k : ℕ)
    (hf : weightProjection k f.val = f.val) (j : Fin (freeDimension a s p))
    (hj : D.weight j ≠ k) : D.basis.equivFun f j = 0 := by
  classical
  have hb (i : Fin (freeDimension a s p)) :
      weightProjection k (D.basis i).val = if D.weight i = k then (D.basis i).val else 0 := by
    rw [(modelBasisWord_spec D i).2.2, weightProjection_truncatedBracket, modelBasisWord_weight]
  let g : formalSpan a s p := ∑ i, D.basis.equivFun f i •
    (if D.weight i = k then D.basis i else 0)
  have hg : g = f := by
    apply Subtype.ext
    have hsum := congrArg Subtype.val (D.basis.sum_equivFun f)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    rw [← hf, ← hsum, map_sum]
    simp only [g, Submodule.coe_sum, Submodule.coe_smul, map_smul, hb]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have he0 : D.basis.equivFun g j = 0 := by
    simp only [g, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hij : i = j
    · subst i
      simp only [ite_eq_right hj, map_zero, Pi.zero_apply, smul_zero]
    · by_cases hi : D.weight i = k
      · rw [ite_eq_left hi, Module.Basis.equivFun_self]
        simp only [hij, ite_false, smul_zero]
      · simp only [ite_eq_right hi, map_zero, Pi.zero_apply, smul_zero]
  rw [hg] at he0
  exact he0

/-- The retained-word expansion uses only basis words of the same
weighted length, with constants independent of the evaluation point. -/
theorem wordLieElement_basis_coordinate_zero {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (I : List (Fin a)) (j : Fin (freeDimension a s p))
    (hj : D.weight j ≠ wordWeight p I) : D.basis.equivFun (wordLieElement I) j = 0 := by
  apply formal_basis_coordinate_zero_of_homogeneous D _ (wordWeight p I) _ j hj
  change weightProjection (wordWeight p I) (truncatedBracket I) = truncatedBracket I
  rw [weightProjection_truncatedBracket]
  simp only [ite_true]
end RothschildStein.L1
