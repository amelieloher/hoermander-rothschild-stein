-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped unitInterval

namespace RothschildStein.G4

/-- Continuous lifts through a local chart are unique from one common
starting point (BB Proposition 9.52, pp. 447–450). This proves uniqueness;
the quantitative existence and interior bounds are separate steps. -/
theorem chart_lift_unique {E X A : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace A] [T2Space E] [PreconnectedSpace A]
    {p : E → X} (hp : IsLocalHomeomorph p) {g₁ g₂ : A → E}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  (T2Space.isSeparatedMap p).eq_of_comp_eq hp.isLocallyInjective h₁ h₂ he a ha

end RothschildStein.G4
