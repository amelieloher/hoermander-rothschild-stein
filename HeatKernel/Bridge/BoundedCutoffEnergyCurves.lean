-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SpecifiedGradientEnergyCurves
public import HeatKernel.Bridge.CutoffEssentialBounds
import Mathlib.Tactic.Linter

/-! # Bounded cutoff energy curves for a specified local weak gradient -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Every supplied weak gradient with the local parabolic energy bounds yields
Bochner cutoff curves with an essential spatial L² bound and whose horizontal
gradients use that same representative. -/
theorem IsLocalWeakSolution.exists_bounded_cutoff_energy_curves_of_weak_gradient {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ) (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (u : ℝ → (Fin N → ℝ) → ℝ) (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (hweak : ∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i,
      hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t))
    (hlocal : HasLocalParabolicEnergyBounds I U u g) :
      ∀ J : Set ℝ, IsCompact J → J ⊆ (I : Set ℝ) →
      ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (Fin N → ℝ)) →
      ∃ v : ℝ → energyGraph (N := N) ⊤ (G.horizontalFields hq),
        MemLp v 2 (volume.restrict J) ∧
        essSup (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
          (volume.restrict J) < ⊤ ∧
        (∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          fun x => u t x * φ x) ∧
        ∀ i, ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
          fun x => g i t x * φ x + u t x * fieldDerivative (G.horizontalFields hq i) φ x := by
  intro J hJ hJI φ hφ hc hs
  obtain ⟨v, hv, hrep, hgrad⟩ :=
    hu.exists_cutoff_energy_curves_of_weak_gradient G hq hqpos hw hspan a I U u g
      hweak hlocal J hJ hJI φ hφ hc hs
  refine ⟨v, hv, ?_, hrep, hgrad⟩
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hrep' : ∀ᵐ t ∂volume.restrict J,
      ((v t : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) =ᵐ[
        volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
          fun x => u t x * φ x := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hrep
  have hb : essSup (fun t => eLpNorm (u t) 2
      ((volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict (tsupport φ)))
      (volume.restrict J) < ⊤ := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (hlocal J (tsupport φ) hJ hJI hc hs).1
  have H := essSup_eLpNorm_cutoff_rep_lt_top hc.measurableSet u hC (subset_tsupport φ)
    (fun t => (v t : GradientSpace (N := N) ⊤ q).fst) hrep' hb
  simpa only [Opens.coe_top, Measure.restrict_univ] using H

end HeatKernel
