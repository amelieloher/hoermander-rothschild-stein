-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingControlledProjection
public import RothschildStein.P1.PaddingControlledLift
public import RothschildStein.G1.ControlledBasics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- Projecting a padded connecting path cannot increase its
control cost, including infinite extended distances. -/
theorem controlDistance_padding_projection_le {q n d : ℕ}
    {Ω : Set (Fin n → ℝ)} {U : Set (Fin (n + d) → ℝ)}
    (hU : U ⊆ basePoint ⁻¹' Ω) (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (ξ η : Fin (n + d) → ℝ) :
    controlDistance Ω w X (basePoint ξ) (basePoint η) ≤
      controlDistance U (paddingControlWeights (d := d) w)
        (paddingVectorFields (d := d) X) ξ η := by
  unfold controlDistance
  apply le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hzero, hone⟩
  have h := G1.controlDistance_le_of_curve
    (isControlledCurve_padding_projection hU w X hγ)
  simpa only [controlDistance, hzero, hone] using h

/-- Every base connecting curve lifts on a fixed fiber with
exactly the original control cost, inside the specified product cylinder. -/
theorem controlDistance_padding_lift_le {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (J : Set (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x y : Fin n → ℝ) (z : Fin d → ℝ) (hz : z ∈ J) :
    controlDistance (basePoint ⁻¹' Ω ∩ paddingFiberCLM n d ⁻¹' J)
      (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (joinPoint x z) (joinPoint y z) ≤ controlDistance Ω w X x y := by
  unfold controlDistance
  apply le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hzero, hone⟩
  have h := G1.controlDistance_le_of_curve (isControlledCurve_padding_lift w X hγ z hz)
  simpa only [controlDistance, hzero, hone] using h

/-- Exact equality of the original extended control distance
with the padded distance along every fixed fiber in a product cylinder.
This is the metric identity used for descent of intrinsic Hölder norms. -/
theorem controlDistance_padding_slice_eq {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (J : Set (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (x y : Fin n → ℝ) (z : Fin d → ℝ) (hz : z ∈ J) :
    controlDistance (basePoint ⁻¹' Ω ∩ paddingFiberCLM n d ⁻¹' J)
      (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (joinPoint x z) (joinPoint y z) = controlDistance Ω w X x y := by
  apply le_antisymm (controlDistance_padding_lift_le Ω J w X x y z hz)
  have h := controlDistance_padding_projection_le (Ω := Ω)
    (U := basePoint ⁻¹' Ω ∩ paddingFiberCLM n d ⁻¹' J)
    (fun _ h => h.1) w X (joinPoint x z) (joinPoint y z)
  have hx : basePoint (joinPoint x z) = x := paddingBaseCLM_join n d x z
  have hy : basePoint (joinPoint y z) = y := paddingBaseCLM_join n d y z
  simpa only [hx, hy] using h

end RothschildStein.P1
