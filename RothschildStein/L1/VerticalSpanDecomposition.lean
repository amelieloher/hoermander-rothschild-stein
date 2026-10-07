-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- A tangent subspace containing one nonzero
vertical vector contains the entire vertical line and is the product of
its horizontal projection with that line (BB Proposition 10.17). -/
theorem submodule_eq_horizontal_prod_of_vertical {n : ℕ}
    (S : Submodule ℝ ((Fin n → ℝ) × ℝ)) {t : ℝ}
    (ht : t ≠ 0) (hv : ((0 : Fin n → ℝ),t) ∈ S) :
    S = (S.map (LinearMap.fst ℝ (Fin n → ℝ) ℝ)).prod ⊤ := by
  have hall : ∀ z : ℝ, ((0 : Fin n → ℝ),z) ∈ S := by
    intro z
    have h := S.smul_mem (z/t) hv
    convert h using 1; simp [Prod.smul_mk,div_mul_cancel₀ z ht]
  ext v
  constructor
  · intro h
    exact ⟨⟨v,h,rfl⟩,Submodule.mem_top⟩
  · rintro ⟨hx,_⟩
    obtain ⟨w,hw,he⟩ := hx
    have h := S.add_mem hw (hall (v.2-w.2))
    convert h using 1
    apply Prod.ext
    · exact he.symm.trans (add_zero _).symm
    · change v.2 = w.2 + (v.2-w.2)
      ring
end RothschildStein.L1
