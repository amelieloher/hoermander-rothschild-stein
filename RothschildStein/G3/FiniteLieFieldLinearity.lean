-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFields
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Actual fields attached to finite Lie coefficients depend linearly
on those coefficients (BB Lemma 9.22, pp. 413–414). -/
def finiteLieFieldLinear {a s N : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) :
    formalSpan a s p →ₗ[ℝ] ((Fin N → ℝ) → (Fin N → ℝ)) where
  toFun := finiteLieField D X
  map_add' f g := by
    funext x
    simp only [finiteLieField, map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r f := by
    funext x
    simp only [finiteLieField, map_smul, Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

/-- The concrete field linear map agrees pointwise with its definition. -/
theorem finiteLieFieldLinear_apply {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (f : formalSpan a s p) : finiteLieFieldLinear D X f = finiteLieField D X f := rfl

end RothschildStein.G3
