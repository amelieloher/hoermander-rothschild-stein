-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalFormResolvent
public import HeatKernel.Semigroup.InverseResolventGraph

/-! # Identification of the horizontal form operator

The weak form graph equals the graph defined by the bounded resolvent. In particular its
domain is the range of that resolvent and its adjoint graph is the same graph.
-/

@[expose] public section
open Set TopologicalSpace

namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem horizontalFormGraph_iff_inverseResolventGraph
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (w g : SpatialL2 U) :
    (∃ u : energyGraph U X, energyInclusion U X u = w ∧
      ∀ v, horizontalEnergy U X u v = inner ℝ g (energyInclusion U X v)) ↔
      InverseResolventGraph (horizontalFormResolvent U X) w g := by
  rw [inverseResolventGraph_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact (horizontalFormEquation_iff_resolvent_eq U X hX u g).mp hu
  · intro h
    let u : energyGraph U X :=
      ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := energyGraph U X) (F := SpatialL2 U)
        (energyInclusion U X) (w + g)
    have hu : energyInclusion U X u = w := h
    refine ⟨u, hu, ?_⟩
    apply (horizontalFormEquation_iff_resolvent_eq U X hX u g).mpr
    rw [hu]
    exact h

end HeatKernel
