-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology
namespace HeatKernel

attribute [local irreducible] energyGraph

/-- Negating an energy vector negates its function representative almost everywhere. -/
theorem energyInclusion_neg_ae {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u : energyGraph (N := N) ⊤ X) :
    energyInclusion ⊤ X (-u) =ᵐ[volume] -⇑(energyInclusion ⊤ X u) := by
  rw [(energyInclusion ⊤ X).map_neg]
  simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_neg (energyInclusion ⊤ X u)

/-- Negating an energy vector negates each derivative representative almost everywhere. -/
theorem energyGradient_neg_ae {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u : energyGraph (N := N) ⊤ X) (i : Fin q) :
    energyGradient ⊤ X (-u) i =ᵐ[volume] -⇑(energyGradient ⊤ X u i) := by
  have he : energyGradient ⊤ X (-u) i = -(energyGradient ⊤ X u i) :=
    congrArg (fun a : PiLp 2 (fun _ : Fin q => SpatialL2 ⊤) => a i)
      ((energyGradient ⊤ X).map_neg u)
  rw [he]
  simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.coeFn_neg (energyGradient ⊤ X u i)

/-- A three-term linear combination of energy vectors has the corresponding function
representative almost everywhere. -/
theorem energyInclusion_sub_add_ae {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u v w : energyGraph (N := N) ⊤ X) :
    energyInclusion ⊤ X (u - v + w) =ᵐ[volume]
      (⇑(energyInclusion ⊤ X u) - ⇑(energyInclusion ⊤ X v) + ⇑(energyInclusion ⊤ X w)) := by
  rw [(energyInclusion ⊤ X).map_add, (energyInclusion ⊤ X).map_sub]
  have hz := (Lp.coeFn_add (energyInclusion ⊤ X u - energyInclusion ⊤ X v)
    (energyInclusion ⊤ X w)).trans
    ((Lp.coeFn_sub (energyInclusion ⊤ X u) (energyInclusion ⊤ X v)).add EventuallyEq.rfl)
  simpa only [Opens.coe_top, Measure.restrict_univ] using hz

/-- A three-term linear combination has the corresponding derivative representatives
almost everywhere. -/
theorem energyGradient_sub_add_ae {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u v w : energyGraph (N := N) ⊤ X) (i : Fin q) :
    energyGradient ⊤ X (u - v + w) i =ᵐ[volume]
      (⇑(energyGradient ⊤ X u i) - ⇑(energyGradient ⊤ X v i) + ⇑(energyGradient ⊤ X w i)) := by
  have he : energyGradient ⊤ X (u - v + w) i =
      energyGradient ⊤ X u i - energyGradient ⊤ X v i + energyGradient ⊤ X w i := by
    rw [(energyGradient ⊤ X).map_add, (energyGradient ⊤ X).map_sub]
    rfl
  rw [he]
  have hz := (Lp.coeFn_add (energyGradient ⊤ X u i - energyGradient ⊤ X v i)
    (energyGradient ⊤ X w i)).trans
    ((Lp.coeFn_sub (energyGradient ⊤ X u i) (energyGradient ⊤ X v i)).add EventuallyEq.rfl)
  simpa only [Opens.coe_top, Measure.restrict_univ] using hz

end HeatKernel
