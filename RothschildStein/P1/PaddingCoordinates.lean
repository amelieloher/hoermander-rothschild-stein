-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingCoordinateDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Joining a point with added coordinates preserves its base. -/
theorem paddingBaseCLM_join (n d : ℕ) (x : Fin n → ℝ) (z : Fin d → ℝ) :
    paddingBaseCLM n d (joinPoint x z) = x := by
  ext j
  simp [paddingBaseCLM, joinPoint]

/-- Joining a point with added coordinates preserves its fiber. -/
theorem paddingFiberCLM_join (n d : ℕ) (x : Fin n → ℝ) (z : Fin d → ℝ) :
    paddingFiberCLM n d (joinPoint x z) = z := by
  ext j
  simp [paddingFiberCLM, joinPoint]

/-- The original and added coordinate projections reconstruct
an arbitrary point, including either empty coordinate block. -/
theorem paddingJoinCLM_projections (n d : ℕ) (ξ : Fin (n + d) → ℝ) :
    paddingJoinCLM n d (paddingBaseCLM n d ξ, paddingFiberCLM n d ξ) = ξ := by
  rw [paddingJoinCLM_apply]
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [joinPoint, paddingBaseCLM]
  · intro i
    simp [joinPoint, paddingFiberCLM]

/-- The product carrier and the joined-coordinate carrier
are continuously linearly equivalent. This is coordinate infrastructure
for diffusion padding, not padding an already constructed group. -/
def paddingCoordinates (n d : ℕ) :
    (Fin (n + d) → ℝ) ≃L[ℝ] ((Fin n → ℝ) × (Fin d → ℝ)) where
  toFun ξ := (paddingBaseCLM n d ξ, paddingFiberCLM n d ξ)
  invFun p := paddingJoinCLM n d p
  left_inv := paddingJoinCLM_projections n d
  right_inv := by
    intro p
    rcases p with ⟨x, z⟩
    change (paddingBaseCLM n d (paddingJoinCLM n d (x, z)),
      paddingFiberCLM n d (paddingJoinCLM n d (x, z))) = (x, z)
    rw [paddingJoinCLM_apply, paddingBaseCLM_join, paddingFiberCLM_join]
  map_add' := by intro x y; simp
  map_smul' := by intro r x; simp
  continuous_toFun := (paddingBaseCLM n d).continuous.prodMk (paddingFiberCLM n d).continuous
  continuous_invFun := (paddingJoinCLM n d).continuous

end RothschildStein.P1
