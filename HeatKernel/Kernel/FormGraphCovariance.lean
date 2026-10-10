-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalOperatorGraph

/-! # Operator graph covariance from horizontal form covariance

An invertible energy-domain map that intertwines the spatial inclusion
and scales the bilinear form transports the associated operator graph.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

namespace HeatKernel

/-- Bilinear form covariance and spatial isometry transport the horizontal operator graph. -/
theorem inverseResolventGraph_horizontalForm_of_energy_covariance {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → Fin N → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (A : SpatialL2 U →L[ℝ] SpatialL2 U)
    (E : energyGraph U X ≃L[ℝ] energyGraph U X) (c : ℝ)
    (hJ : ∀ v, energyInclusion U X (E v) = A (energyInclusion U X v))
    (hinner : ∀ f g, inner ℝ (A f) (A g) = inner ℝ f g)
    (henergy : ∀ v w, horizontalEnergy U X (E v) (E w) = c * horizontalEnergy U X v w)
    {u g : SpatialL2 U} (hu : InverseResolventGraph (horizontalFormResolvent U X) u g) :
    InverseResolventGraph (horizontalFormResolvent U X) (A u) (c • A g) := by
  obtain ⟨v, hv, hform⟩ := (horizontalFormGraph_iff_inverseResolventGraph U X hX u g).mpr hu
  apply (horizontalFormGraph_iff_inverseResolventGraph U X hX _ _).mp
  refine ⟨E v, by rw [hJ, hv], ?_⟩
  intro w
  have hinc : energyInclusion U X w = A (energyInclusion U X (E.symm w)) := by
    rw [← hJ, E.apply_symm_apply]
  calc
    horizontalEnergy U X (E v) w =
        horizontalEnergy U X (E v) (E (E.symm w)) := by rw [E.apply_symm_apply]
    _ = c * horizontalEnergy U X v (E.symm w) := henergy v (E.symm w)
    _ = c * inner ℝ g (energyInclusion U X (E.symm w)) := by rw [hform]
    _ = inner ℝ (c • A g) (energyInclusion U X w) := by
      rw [real_inner_smul_left, hinc, hinner]

end HeatKernel
