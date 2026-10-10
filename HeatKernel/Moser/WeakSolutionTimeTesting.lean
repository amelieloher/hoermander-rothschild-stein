-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyRepresentatives
public import HeatKernel.Moser.WeakSolutionSpatialEnergyIdentity
public import HeatKernel.Moser.WeakSolutionConvexEnergy
public import HeatKernel.Moser.WeakSolutionDualFluxIntegrability

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Compact temporal testing of spatially weighted weak solutions

The original, unaveraged flux pairs with the nonlinear spatial test. Local square
integrability and the scalar energy representative are consequences of the weak
cutoff pair, so no additional time derivative or energy regularity is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped NNReal
namespace HeatKernel

/-- The nonlinear spatial test paired with the original dual flux is locally
integrable, by the two square-integrable curves of the weak cutoff pair. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.integrable_spatial_energy_flux
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {J : Set ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff J u g φ k v F)
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest) :
    IntegrableOn (fun t => F t (W.energyMap hX T (v t))) J := by
  have hmap := W.multiplier.comp_memLp' (T.memLp_energyMap V X hX hp.1)
  exact integrable_dual_apply_of_memLp_two hp.2.2.2.2.1 hmap

/-- On every compact interior time interval, the scalar nonlinear energy of a weak
cutoff pair has an absolutely continuous representative with the original flux as
its negative derivative. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_spatial_energy_representative
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e A B ∧
      e =ᵐ[volume.restrict (Icc a b)] (fun t => W.energy T (v t)) ∧
      (∀ᵐ t ∂volume, t ∈ Icc A B →
        HasDerivAt e (-F t (W.energyMap hX T (v t))) t) := by
  apply exists_absolutelyContinuous_energy_representative_of_ae_endpoint_identity
    (hp.integrable_spatial_energy_flux hX W T) hab hAa hbB
  filter_upwards [hp.ae_local_spatial_energy_endpoint_identity hX] with s hs
  filter_upwards [hs] with t ht
  exact ht W T

/-- The nonlinear scalar energy is integrable on every compact interior time
interval, without assuming a pointwise continuous representative of the solution. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.integrableOn_spatial_energy
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    IntegrableOn (fun t => W.energy T (v t)) (Icc a b) := by
  obtain ⟨e, hac, heq, _⟩ := hp.exists_spatial_energy_representative hX W T hab hAa hbB
  have hsub : Icc a b ⊆ uIcc A B := by
    rw [uIcc_of_le (show A ≤ B by linarith)]
    exact fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  exact (hac.continuousOn.mono hsub).integrableOn_Icc.congr heq

end HeatKernel
