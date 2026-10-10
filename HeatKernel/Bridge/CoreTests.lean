-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalSobolev
public import HeatKernel.Form.ZeroBoundaryCore
public import HeatKernel.Form.CoefficientContinuity
import Mathlib.Tactic.Linter

/-! # Extending smooth test identities to zero-boundary energy tests

Graph-norm density extends any continuous scalar test functional. Applying this
to the measurable-coefficient bilinear form gives the stationary energy-test
identity from its smooth compact test version.
-/

@[expose] public section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace HeatKernel

/-- A continuous scalar functional vanishing on the interior core vanishes on its closure. -/
theorem eq_zero_on_zeroBoundaryGraph_of_eq_zero_on_core {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {F : energyGraph (N := N) ⊤ X → ℝ} (hF : Continuous F)
    (hcore : ∀ w : energyGraph (N := N) ⊤ X,
      (w : GradientSpace (N := N) ⊤ q) ∈ interiorGradientPairs U X → F w = 0)
    (v : zeroBoundaryGraph U X) :
    F ⟨v, zeroBoundaryGraph_le_energyGraph U X v.property⟩ = 0 := by
  obtain ⟨w, hw, ht⟩ := exists_interiorGradientPairs_tendsto U X v
  let e : ℕ → energyGraph (N := N) ⊤ X := fun n =>
    ⟨w n, zeroBoundaryGraph_le_energyGraph U X
      (interiorGradientPairs_subset_zeroBoundaryGraph U X (hw n))⟩
  have he : Tendsto e atTop (𝓝 (⟨v, zeroBoundaryGraph_le_energyGraph U X v.property⟩ :
      energyGraph (N := N) ⊤ X)) := tendsto_subtype_rng.mpr ht
  have heF := hF.continuousAt.tendsto.comp he
  have hz : Tendsto (fun n => F (e n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [show (fun n => F (e n)) = fun _ => 0 from
      funext (fun n => hcore (e n) (hw n))] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique heF hz

end HeatKernel
