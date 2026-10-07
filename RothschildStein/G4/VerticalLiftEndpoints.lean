-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.RectangularLiftEndpoints

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Function Set Topology unitInterval

namespace RothschildStein.G4

/-- Individual vertical lift existence suffices for the endpoint
argument: choose the lifts, then derive joint continuity from their
continuous initial values (BB Thm 9.47 and Prop 9.55, pp. 440–441, 457–458). -/
theorem rectangular_initial_endpoints_eq_of_vertical_lifts {E X : Type*}
    [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    (p : E → X) (hp : IsLocalHomeomorph p)
    (H : C(I × I, X)) (start : C(I, E))
    (hlifts : ∀ s : I, ∃ θ : C(I, E), θ 0 = start s ∧
      ∀ t : I, p (θ t) = H (t, s))
    (y : X) (hleft : ∀ t, H (t, 0) = y)
    (hright : ∀ t, H (t, 1) = y) (htop : ∀ s, H (1, s) = y) :
    start 0 = start 1 := by
  choose θ hstart hθ using hlifts
  let Γ : I × I → E := fun ts => θ ts.2 ts.1
  have hΓlift : p ∘ Γ = H := by
    funext ts
    exact hθ ts.2 ts.1
  have hzero : Continuous (fun s => Γ (0, s)) :=
    start.continuous.congr (fun s => (hstart s).symm)
  have hvertical : ∀ s, Continuous (fun t => Γ (t, s)) := fun s => (θ s).continuous
  have heq := rectangular_lift_initial_endpoints_eq p hp H Γ hΓlift hzero hvertical
    y hleft hright htop
  change θ 0 0 = θ 1 0 at heq
  rwa [hstart 0, hstart 1] at heq

end RothschildStein.G4
