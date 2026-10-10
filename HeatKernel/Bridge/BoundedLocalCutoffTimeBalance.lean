-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalBoundedDualEnergy
public import HeatKernel.Bridge.CutoffDualValueIdentification
import Mathlib.Tactic.Linter

/-! # Weak time equations for bounded local cutoff energy values -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Every energy representative of a bounded local energy cutoff satisfies the
localized dual weak time equation with a square-integrable flux curve. -/
theorem HasLocalDualEnergyCurves.exists_bounded_cutoff_energy_time_balance {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : HasLocalDualEnergyCurves X a I U u g)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    (hloc : MemLocalEnergy ⊤ X φ) (hk : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (k i))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂volume, ‖φ x‖ ≤ C) (hkb : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ L)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ)))
    (v : ℝ → energyGraph (N := N) ⊤ X)
    (hv : ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x) :
    ∃ F : ℝ → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ),
      MemLp F 2 (volume.restrict J) ∧
      (∀ᵐ t ∂volume.restrict J, ∀ w : energyGraph (N := N) ⊤ X,
        F t w = ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
          (φ x * (w : GradientSpace (N := N) ⊤ q).snd i x +
            k i x * (w : GradientSpace (N := N) ⊤ q).fst x)) ∧
      SatisfiesDualTimeBalance J
        (fun t => spatialValueFunctional ⊤ X (v t : GradientSpace (N := N) ⊤ q).fst) F := by
  obtain ⟨D, F, hpair⟩ := h.exists_bounded_interior_cutoff_pair hX hJ hJI hloc hk hC hL hb hkb hc hs
  exact ⟨F, hpair.2.1, hpair.2.2.2.1, hpair.cutoff_value_time_balance X v hv⟩

end HeatKernel
