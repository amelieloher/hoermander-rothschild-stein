-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The invertible block derivative of the full parameter/coordinate map. -/
def blockDerivativeEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (B : E ≃L[ℝ] E) : (E × E) ≃L[ℝ] (E × E) where
  toFun p := (p.1,A p.1+B p.2)
  invFun q := (q.1,B.symm (q.2-A q.1))
  left_inv p := by simp only [add_sub_cancel_left,ContinuousLinearEquiv.symm_apply_apply,Prod.mk.eta]
  right_inv q := by simp only [ContinuousLinearEquiv.apply_symm_apply,add_sub_cancel,Prod.mk.eta]
  map_add' p q := by simp only [Prod.fst_add,Prod.snd_add,map_add,Prod.mk_add_mk]; abel_nf
  map_smul' r p := by
    change (r • p.1,A (r • p.1)+B (r • p.2)) =
      (r • p.1,r • (A p.1+B p.2))
    simp only [map_smul,smul_add]
  continuous_toFun := continuous_fst.prodMk ((A.continuous.comp continuous_fst).add
    (B.continuous.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk (B.symm.continuous.comp
    (continuous_snd.sub (A.continuous.comp continuous_fst)))

/-- The block equivalence is exactly the
continuous linear derivative of the full forward map. -/
theorem blockDerivativeEquiv_toCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (B : E ≃L[ℝ] E) :
    (blockDerivativeEquiv A B : (E × E) →L[ℝ] (E × E)) =
      (ContinuousLinearMap.fst ℝ E E).prod (A.coprod (B : E →L[ℝ] E)) := by
  ext p <;> rfl
end RothschildStein.L1
