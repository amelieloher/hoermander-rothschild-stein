-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantFields
public import Mathlib.LinearAlgebra.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Left-invariant fields form a vector subspace (BB Proposition 3.26, p. 109). -/
def leftInvariantSubmodule : Submodule ℝ ((Fin N → ℝ) → (Fin N → ℝ)) where
  carrier := {V | IsLeftInvariantField G V}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro V W hV hW x y
    change fderiv ℝ (G.mul x) y (V y + W y) = V (G.mul x y) + W (G.mul x y)
    rw [map_add, hV x y, hW x y]
  smul_mem' := by
    intro c V hV x y
    change fderiv ℝ (G.mul x) y (c • V y) = c • V (G.mul x y)
    rw [map_smul, hV x y]

/-- An invariant field is the constant linear combination prescribed by its value
at zero (BB Proposition 3.26, p. 110). -/
theorem IsLeftInvariantField.canonical_expansion
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (hV : IsLeftInvariantField G V) (x : Fin N → ℝ) :
    V x = ∑ j, V 0 j • G.canonicalField j x := by
  have hv : V 0 = ∑ j, V 0 j • Hormander.Interface.basisVec j := by
    ext k
    simp [Hormander.Interface.basisVec, Pi.single_apply]
  calc
    V x = fderiv ℝ (G.mul x) 0 (V 0) := congrFun (hV.eq_leftField G) x
    _ = fderiv ℝ (G.mul x) 0 (∑ j, V 0 j • Hormander.Interface.basisVec j) :=
      congrArg (fderiv ℝ (G.mul x) 0) hv
    _ = _ := by simp [map_sum, HomogeneousGroup.canonicalField]

end RothschildStein.G2
