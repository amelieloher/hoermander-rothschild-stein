-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.VerticalSpanRank
public import RothschildStein.P1.PaddingCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Coordinates identifying the one-variable extension with base times scalar. -/
def oneVariableCoordinates (n : ℕ) :
    (Fin (n+1) → ℝ) ≃ₗ[ℝ] ((Fin n → ℝ) × ℝ) :=
  (P1.paddingCoordinates n 1).toLinearEquiv.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (Fin n → ℝ))
      (LinearEquiv.funUnique (Fin 1) ℝ ℝ))

/-- The joined-coordinate tangent carrier
has exactly one more dimension than its horizontal image whenever its
subspace contains an actual nonzero vertical vector. -/
theorem finrank_eq_base_add_one_of_vertical {n : ℕ}
    (S : Submodule ℝ (Fin (n+1) → ℝ)) {v : Fin (n+1) → ℝ}
    (hv : v ∈ S) (hb : P1.paddingBaseCLM n 1 v = 0)
    (ht : P1.paddingFiberCLM n 1 v 0 ≠ 0) :
    Module.finrank ℝ S = Module.finrank ℝ (S.map (P1.paddingBaseCLM n 1).toLinearMap) + 1 := by
  let e := oneVariableCoordinates n
  have hmem : ((0 : Fin n → ℝ),P1.paddingFiberCLM n 1 v 0) ∈ S.map e.toLinearMap := by
    refine ⟨v,hv,?_⟩
    change (P1.paddingBaseCLM n 1 v,P1.paddingFiberCLM n 1 v 0) = _
    rw [hb]
  have he := finrank_eq_horizontal_add_one_of_vertical (S.map e.toLinearMap) ht hmem
  rw [e.finrank_map_eq S] at he
  have hmap : (S.map e.toLinearMap).map (LinearMap.fst ℝ (Fin n → ℝ) ℝ) =
      S.map (P1.paddingBaseCLM n 1).toLinearMap := by
    rw [← Submodule.map_comp]
    rfl
  rwa [hmap] at he
end RothschildStein.L1
