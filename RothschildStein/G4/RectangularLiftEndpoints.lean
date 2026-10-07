-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Function Set Topology unitInterval

namespace RothschildStein.G4

/-- Vertical lifts of a loop contraction are jointly continuous,
and the two initial endpoints agree because its three other edges lift
into discrete fibers (BB Thm 9.47 and Prop 9.55, pp. 440–441, 457–458). -/
theorem rectangular_lift_initial_endpoints_eq {E X : Type*}
    [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    (p : E → X) (hp : IsLocalHomeomorph p)
    (H : C(I × I, X)) (Γ : I × I → E) (hlift : p ∘ Γ = H)
    (hzero : Continuous (fun s => Γ (0, s)))
    (hvertical : ∀ s, Continuous (fun t => Γ (t, s)))
    (y : X) (hleft : ∀ t, H (t, 0) = y)
    (hright : ∀ t, H (t, 1) = y) (htop : ∀ s, H (1, s) = y) :
    Γ (0, 0) = Γ (0, 1) := by
  have hsep : IsSeparatedMap p := T2Space.isSeparatedMap p
  have hΓ : Continuous Γ := hp.continuous_lift hsep H hlift hzero hvertical
  have hpoint : ∀ t s, p (Γ (t, s)) = H (t, s) :=
    fun t s => congr_fun hlift (t, s)
  have he₀ : Γ (0, 0) = Γ (1, 0) :=
    hsep.const_of_comp hp.isLocallyInjective (hvertical 0)
      (fun t t' => (hpoint t 0).trans ((hleft t).trans ((hleft t').symm.trans
        (hpoint t' 0).symm))) 0 1
  have he₁ : Γ (1, 1) = Γ (0, 1) :=
    hsep.const_of_comp hp.isLocallyInjective (hvertical 1)
      (fun t t' => (hpoint t 1).trans ((hright t).trans ((hright t').symm.trans
        (hpoint t' 1).symm))) 1 0
  have heTop : Γ (1, 0) = Γ (1, 1) :=
    hsep.const_of_comp hp.isLocallyInjective (hΓ.comp (Continuous.prodMk_right 1))
      (fun s s' => (hpoint 1 s).trans ((htop s).trans ((htop s').symm.trans
        (hpoint 1 s').symm))) 0 1
  exact he₀.trans (heTop.trans he₁)

end RothschildStein.G4
