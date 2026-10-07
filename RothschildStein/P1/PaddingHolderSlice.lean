-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingControlDistance
public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.Definitions.holderENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- The P2 cylinder is the exact product cylinder of the
padding coordinate projections. -/
theorem padding_cylinder_eq {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ)) :
    (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) =
      basePoint ⁻¹' (Ω : Set (Fin n → ℝ)) ∩
        paddingFiberCLM n d ⁻¹' (J : Set (Fin d → ℝ)) := by
  ext ξ
  rfl

/-- Exact fixed-fiber distance identity on the shared P2 cylinder. -/
theorem controlDistance_padding_cylinder_slice_eq {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x y : Fin n → ℝ) (z : Fin d → ℝ) (hz : z ∈ (J : Set (Fin d → ℝ))) :
    controlDistance (P2.cylinder Ω J : Set (Fin (n + d) → ℝ))
      (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (joinPoint x z) (joinPoint y z) = controlDistance (Ω : Set (Fin n → ℝ)) w X x y := by
  rw [padding_cylinder_eq]
  exact controlDistance_padding_slice_eq _ _ w X x y z hz

end RothschildStein.P1
