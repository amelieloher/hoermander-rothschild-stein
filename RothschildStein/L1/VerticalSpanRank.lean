-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.VerticalSpanDecomposition
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- A tangent subspace with a vertical line is
linearly equivalent to its horizontal projection times the added scalar. -/
def verticalSpanEquiv {n : ℕ} (S : Submodule ℝ ((Fin n → ℝ) × ℝ))
    (h : S = (S.map (LinearMap.fst ℝ (Fin n → ℝ) ℝ)).prod ⊤) :
    S ≃ₗ[ℝ] ((S.map (LinearMap.fst ℝ (Fin n → ℝ) ℝ)) × ℝ) where
  toFun v := (⟨v.val.1,⟨v.val,v.property,rfl⟩⟩,v.val.2)
  invFun w := ⟨(w.1.val,w.2),by
    have hh : (w.1.val,w.2) ∈ (S.map (LinearMap.fst ℝ (Fin n → ℝ) ℝ)).prod ⊤ :=
      ⟨w.1.property,Submodule.mem_top⟩
    exact (congrArg (fun T : Submodule ℝ ((Fin n → ℝ) × ℝ) => (w.1.val,w.2) ∈ T) h).mpr hh⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv w := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · rfl
  map_add' v w := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · rfl
  map_smul' t v := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · rfl

/-- One nonzero vertical tangent combination
raises the horizontal rank by exactly one (BB Proposition 10.17). -/
theorem finrank_eq_horizontal_add_one_of_vertical {n : ℕ}
    (S : Submodule ℝ ((Fin n → ℝ) × ℝ)) {t : ℝ}
    (ht : t ≠ 0) (hv : ((0 : Fin n → ℝ),t) ∈ S) :
    Module.finrank ℝ S =
      Module.finrank ℝ (S.map (LinearMap.fst ℝ (Fin n → ℝ) ℝ)) + 1 := by
  have he := (verticalSpanEquiv S (submodule_eq_horizontal_prod_of_vertical S ht hv)).finrank_eq
  simpa only [Module.finrank_prod,Module.finrank_self] using he
end RothschildStein.L1
