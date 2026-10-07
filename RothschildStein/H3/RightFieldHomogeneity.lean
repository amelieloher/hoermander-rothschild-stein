-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OppositeGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- far part. The right-invariant field with the same identity
value as a homogeneous field has the same degree. This supplies the
right fields in the integration-by-parts kernel (BB p. 383). -/
theorem rightField_identity_value_homogeneous
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {degree : ℝ}
    (hV : IsHomogeneousField G V degree) :
    IsHomogeneousField G (rightField G (V 0)) degree := by
  intro t ht x
  have hv := hV t ht 0
  rw [dilate_zero G t] at hv
  have hh := dilate_leftField (oppositeGroup G) t ht (V 0) x
  have he : G.dilate t (rightField G (V 0) x) =
      rightField G (G.dilate t (V 0)) (G.dilate t x) := by
    simpa only [oppositeGroup_leftField, oppositeGroup_dilate] using hh
  rw [he, hv]
  simp only [rightField, map_smul]

end RothschildStein.H3
