-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.UniformParabolicEnergyTests
public import HeatKernel.Bridge.SpecifiedGradientEnergyCurves
public import HeatKernel.Bridge.StationaryEnergyIdentity
import Mathlib.Tactic.Linter

/-! # A common weak gradient for stationary identities and Bochner cutoff curves -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Measurable symmetric ellipticity yields one weak gradient carrying local energy
bounds, every stationary energy identity, and all Bochner cutoff energy curves. -/
theorem IsLocalWeakSolution.exists_stationary_energy_witness {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
      ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    : ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      (∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i,
        hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t)) ∧
      HasLocalParabolicEnergyBounds I U u g ∧
      HasStationaryEnergyTestIdentity (G.horizontalFields hq) a I U u g ∧
      ∀ J : Set ℝ, IsCompact J → J ⊆ (I : Set ℝ) →
      ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (Fin N → ℝ)) →
      ∃ v : ℝ → energyGraph (N := N) ⊤ (G.horizontalFields hq),
        MemLp v 2 (volume.restrict J) ∧
        (∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          fun x => u t x * φ x) ∧
        ∀ i, ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
          fun x => g i t x * φ x + u t x * fieldDerivative (G.horizontalFields hq i) φ x := by
  obtain ⟨g, hg, hb, he⟩ :=
    hu.exists_uniform_energy_test_identity G hq hqpos hw hspan a I U ha hlower hbound
  exact ⟨g, hg, hb, he,
    hu.exists_cutoff_energy_curves_of_weak_gradient G hq hqpos hw hspan a I U u g hg hb⟩

end HeatKernel
