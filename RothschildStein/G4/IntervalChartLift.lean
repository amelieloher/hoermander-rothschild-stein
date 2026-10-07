-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VerticalLiftEndpoints
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function Topology unitInterval

namespace RothschildStein.G4

/-- An actual real-interval chart lift supplies the subtype-valued
continuous lift required by the homotopy topology provider. -/
theorem exists_continuousMap_chart_lift {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (Q : Set (Fin n → ℝ))
    (γ θ : ℝ → (Fin n → ℝ)) (u₀ : Q)
    (hcont : ContinuousOn θ (Icc (0 : ℝ) 1)) (hstart : θ 0 = u₀.val)
    (hmap : MapsTo θ (Icc (0 : ℝ) 1) Q)
    (hlift : EqOn (F ∘ θ) γ (Icc (0 : ℝ) 1)) :
    ∃ Θ : C(I, Q), Θ 0 = u₀ ∧ ∀ t : I, F (Θ t).val = γ t.val := by
  let Θ : C(I, Q) :=
    { toFun := fun t => ⟨θ t.val, hmap t.property⟩
      continuous_toFun := hcont.domRestrict.subtype_mk _ }
  refine ⟨Θ, ?_, fun t => hlift t.property⟩
  apply Subtype.ext
  exact hstart

end RothschildStein.G4
