-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualChartLocalHomeomorph
public import RothschildStein.G4.LiftContinuity
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Two lifts staying in the actual open chart box agree on an
interval if they agree initially. Local invertibility is required only
on that box, rather than throughout the ambient space
(BB Prop 9.52, p. 449). -/
theorem local_chart_lift_unique_on {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [T2Space E] {U : Set E} (hU : IsOpen U)
    (F : E → X) (hF : IsLocalHomeomorphOn F U)
    {a b : ℝ} (hab : a ≤ b) (θ₁ θ₂ : ℝ → E)
    (h₁ : ContinuousOn θ₁ (Icc a b)) (h₂ : ContinuousOn θ₂ (Icc a b))
    (hU₁ : MapsTo θ₁ (Icc a b) U) (hU₂ : MapsTo θ₂ (Icc a b) U)
    (hlift : EqOn (F ∘ θ₁) (F ∘ θ₂) (Icc a b))
    (hstart : θ₁ a = θ₂ a) : EqOn θ₁ θ₂ (Icc a b) := by
  let g₁ : Icc a b → U := fun t => ⟨θ₁ t, hU₁ t.property⟩
  let g₂ : Icc a b → U := fun t => ⟨θ₂ t, hU₂ t.property⟩
  have hcont₁ : Continuous g₁ := h₁.domRestrict.subtype_mk (fun t => hU₁ t.property)
  have hcont₂ : Continuous g₂ := h₂.domRestrict.subtype_mk (fun t => hU₂ t.property)
  have hlocal : IsLocalHomeomorph (fun u : U => F u) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hF.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun u _ => u.property))
  have heq : (fun u : U => F u) ∘ g₁ = (fun u : U => F u) ∘ g₂ :=
    funext (fun t => hlift t.property)
  let intervalPreconnectedSpace : PreconnectedSpace (Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hg := chart_lift_unique hlocal hcont₁ hcont₂ heq
    (⟨a, ⟨le_rfl, hab⟩⟩ : Icc a b) (Subtype.ext hstart)
  intro t ht
  exact congrArg Subtype.val (congrFun hg ⟨t, ht⟩)

end RothschildStein.G4
