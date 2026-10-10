-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CutoffEnergyTimeIdentity
import Mathlib.Tactic.Linter

/-! # Compatible cutoff evolution curves for a specified weak gradient -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Local energy bounds and local dual balances for a specified weak gradient
give compatible cutoff energy curves with their dual time equations. -/
theorem IsLocalWeakSolution.hasCutoffEnergyTimeCurves_of_weak_gradient {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ)
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (hg : ∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i,
      hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t))
    (hb : HasLocalParabolicEnergyBounds I U u g)
    (hd : HasLocalDualEnergyCurves (G.horizontalFields hq) a I U u g) :
    HasCutoffEnergyTimeCurves (G.horizontalFields hq) a I U u g := by
  intro J hJ hJI φ hφ hc hs
  obtain ⟨v, hv, hvb, hvf, hvg⟩ :=
    hu.exists_bounded_cutoff_energy_curves_of_weak_gradient G hq hqpos hw hspan a I U u g
      hg hb J hJ hJI φ hφ hc hs
  obtain ⟨F, hF, hFr, ht⟩ := hd.exists_cutoff_energy_time_balance
    (G.horizontalFields_contDiff hq) hJ hJI hφ hc hs v hvf
  exact ⟨v, F, hv, hvb, hvf, hvg, hF, hFr, ht⟩

end HeatKernel
