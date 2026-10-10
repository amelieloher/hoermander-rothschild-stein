-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompatibleParabolicEnergyWitness
public import HeatKernel.Bridge.LocalDualEnergyBounds
public import HeatKernel.Bridge.SpecifiedZeroBoundaryCutoffCurves
public import HeatKernel.Bridge.SpecifiedCutoffEnergyTimeCurves
public import HeatKernel.Bridge.ParabolicCoefficientBounds
import Mathlib.Tactic.Linter

/-! # Compatible cutoff energy curves with their dual time equations -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- One weak gradient carries the local energy bounds, both weak test identities,
dual time balances, zero-boundary cutoff curves, and actual cutoff time equations. -/
theorem IsLocalWeakSolution.exists_cutoff_energy_time_witness {N q : ℕ}
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
      SatisfiesParabolicTestIdentity (G.horizontalFields hq) a I U u g ∧
      HasStationaryEnergyTestIdentity (G.horizontalFields hq) a I U u g ∧
      HasLocalDualEnergyCurves (G.horizontalFields hq) a I U u g ∧
      HasZeroBoundaryCutoffEnergyCurves (G.horizontalFields hq) I U u g ∧
      HasCutoffEnergyTimeCurves (G.horizontalFields hq) a I U u g := by
  obtain ⟨g, hg, hb, ht, he, _⟩ :=
    hu.exists_compatible_parabolic_energy_witness G hq hqpos hw hspan a I U ha hlower hbound
  have hentry (i j : Fin q) : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      ‖a z.1 z.2 i j‖ ≤ upper := by
    simpa only [Measure.restrict_univ] using
      ae_norm_parabolic_coefficient_entry_le a hlower hbound univ i j
  have hd : HasLocalDualEnergyCurves (G.horizontalFields hq) a I U u g :=
    hb.hasLocalDualEnergyCurves he
      (fun J K hJ hJI hK hKU =>
        hu.memLp_two_on_compact_cylinder G hq hqpos hw hspan a I U hJ hJI hK hKU)
      ha hentry
  exact ⟨g, hg, hb, ht, he, hd,
    hu.hasZeroBoundaryCutoffEnergyCurves_of_weak_gradient G hq hqpos hw hspan a I U u g hg hb,
    hu.hasCutoffEnergyTimeCurves_of_weak_gradient G hq hqpos hw hspan a I U u g hg hb hd⟩

end HeatKernel
