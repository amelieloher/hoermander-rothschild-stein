-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HolderIsometricRestriction
public import RothschildStein.P1.PaddingNoDriftHolderSlice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Fixed-fiber Hölder restriction with ambient coefficient
cylinders and independent smaller output cylinders (BB p. 542). -/
theorem holderENorm_padding_ambient_slice_le {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (V : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (α : ℝ) (v : (Fin (n + d) → ℝ) → ℝ)
    (z : Fin d → ℝ) (hzA : z ∈ (JA : Set (Fin d → ℝ)))
    (hz : z ∈ (J : Set (Fin d → ℝ))) :
    holderENorm (controlDistance (Ω : Set (Fin n → ℝ)) w X) α
      (V : Set (Fin n → ℝ)) (fun x => v (joinPoint x z)) ≤
    holderENorm (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
      (paddingControlWeights (d := d) w)
      (paddingVectorFields (d := d) X)) α
      (P2.cylinder V J : Set (Fin (n + d) → ℝ)) v := by
  apply holderENorm_comp_le_of_isometry
  · intro x hx
    exact P2.joinPoint_mem_cylinder.mpr ⟨hx, hz⟩
  · intro x _ y _
    exact controlDistance_padding_cylinder_slice_eq Ω JA w X x y z hzA

/-- Fixed-fiber Hölder restriction with ambient coefficient
cylinders and independent smaller output cylinders (BB p. 542). -/
theorem holderENorm_paddingNoDrift_ambient_slice_le {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (V : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (α : ℝ) (v : (Fin (n + d) → ℝ) → ℝ)
    (z : Fin d → ℝ) (hzA : z ∈ (JA : Set (Fin d → ℝ)))
    (hz : z ∈ (J : Set (Fin d → ℝ))) :
    holderENorm (controlDistance (Ω : Set (Fin n → ℝ)) w X) α
      (V : Set (Fin n → ℝ)) (fun x => v (joinPoint x z)) ≤
    holderENorm (controlDistance (P2.cylinder Ω JA : Set (Fin (n + d) → ℝ))
      (paddingNoDriftWeights (d := d) w)
      (paddingNoDriftVectorFields (d := d) X)) α
      (P2.cylinder V J : Set (Fin (n + d) → ℝ)) v := by
  apply holderENorm_comp_le_of_isometry
  · intro x hx
    exact P2.joinPoint_mem_cylinder.mpr ⟨hx, hz⟩
  · intro x _ y _
    exact controlDistance_paddingNoDrift_cylinder_slice_eq Ω JA w X x y z hzA

end RothschildStein.P1
