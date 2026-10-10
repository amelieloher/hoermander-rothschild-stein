-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalDualEnergyIdentity
public import HeatKernel.Bridge.LocalDualEnergyCurves
import Mathlib.Tactic.Linter

/-! # Constructing local dual curves from local energy bounds -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Bounded measurable coefficients and the stationary identity turn local
energy bounds into compatible dual curves on all compact interior cylinders. -/
theorem HasLocalParabolicEnergyBounds.hasLocalDualEnergyCurves {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hb : HasLocalParabolicEnergyBounds I U u g)
    (he : HasStationaryEnergyTestIdentity X a I U u g)
    (hvalue : ∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
      IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
      MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
        (volume.restrict (J ×ˢ K)))
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    {C : ℝ} (hentry : ∀ i j, ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume, ‖a z.1 z.2 i j‖ ≤ C) :
    HasLocalDualEnergyCurves X a I U u g := by
  intro J K hJ hJI hK hKU V hVK
  have hu : MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using
      hvalue J K hJ hJI hK hKU
  exact HasStationaryEnergyTestIdentity.exists_balanced_dual_curves hb he ha hentry
    hJ hJI hK hKU V hVK hu

end HeatKernel
