-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionTimeTesting
public import HeatKernel.Moser.WeakSolutionAffineEnergyIdentity
import HeatKernel.Moser.TopExhaustionAffineEnergyTrace

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Compact temporal testing with affine primitive corrections

A fixed spatial test restores the constant part of a logarithmic or power test.
Both the corrected energy and the original corrected flux are retained when
constructing the scalar time representative and testing with a temporal weight.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
namespace HeatKernel

variable {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b : ℝ}

/-- The affine-corrected scalar energy has a locally absolutely continuous
representative whose derivative is minus its original affine test flux. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.exists_affine_energy_representative
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (w : zeroBoundaryGraph V X) (c : ℝ)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e A B ∧
      e =ᵐ[volume.restrict (Icc a b)] (fun t => W.affineEnergy T w c (v t)) ∧
      (∀ᵐ t ∂volume, t ∈ Icc A B →
        HasDerivAt e (-F t (W.affineEnergyMap hX T w c (v t))) t) := by
  apply exists_absolutelyContinuous_energy_representative_of_ae_endpoint_identity
    (hp.integrable_affine_energy_flux hX W T w c) hab hAa hbB
  filter_upwards [hp.ae_affine_spatial_energy_endpoint_identity hX] with s hs
  filter_upwards [hs] with t ht
  exact ht W T w c

/-- The corrected scalar energy is integrable on each compact interior interval. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.integrableOn_affine_energy
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (w : zeroBoundaryGraph V X) (c : ℝ)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B) :
    IntegrableOn (fun t => W.affineEnergy T w c (v t)) (Icc a b) := by
  obtain ⟨e, hac, heq, _⟩ := hp.exists_affine_energy_representative hX W T w c hab hAa hbB
  have hsub : Icc a b ⊆ uIcc A B := by
    rw [uIcc_of_le (show A ≤ B by linarith)]
    exact fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  exact (hac.continuousOn.mono hsub).integrableOn_Icc.congr heq

end HeatKernel
