-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SpecifiedGradientEnergyCurves
public import HeatKernel.Bridge.WeakCutoffCurveMultiplication
public import HeatKernel.Bridge.CutoffEssentialBounds
import Mathlib.Tactic.Linter

/-! # Bounded weak-cutoff energy curves for a specified local weak gradient -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A compact bounded spatial cutoff with bounded weak derivatives produces
Bochner energy curves with the same solution gradient and a finite essential
spatial L² bound. -/
theorem IsLocalWeakSolution.exists_bounded_weak_cutoff_energy_curves_of_weak_gradient {N q : ℕ}
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
      ∀ (φ : (Fin N → ℝ) → ℝ) (k : Fin q → (Fin N → ℝ) → ℝ),
      MemLocalEnergy ⊤ (G.horizontalFields hq) φ →
      (∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] φ (k i)) →
      ∀ C L : ℝ, 0 ≤ C → 0 ≤ L →
      (∀ x, ‖φ x‖ ≤ C) → (∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ L) →
      HasCompactSupport φ →
      tsupport φ ⊆ (U : Set (Fin N → ℝ)) →
      ∃ v : ℝ → energyGraph (N := N) ⊤ (G.horizontalFields hq),
        MemLp v 2 (volume.restrict J) ∧
        essSup (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
          (volume.restrict J) < ⊤ ∧
        (∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          fun x => u t x * φ x) ∧
        ∀ i, ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
          fun x => g i t x * φ x + u t x * k i x := by
  intro J hJ hJI φ k hφ hk C L hC hL hb hkb hc hs
  obtain ⟨ψ, P, hP, hφP, _, hψ⟩ := S.exists_test_plateau U ⟨tsupport φ, hc⟩ hs
  obtain ⟨vψ, hvψ, hvalψ, hgradψ⟩ :=
    hu.exists_cutoff_energy_curves_of_weak_gradient G hq hqpos hw hspan a I U u g
      hweak hlocal J hJ hJI ψ ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
  obtain ⟨v, hv, hrep, hgrad⟩ := exists_weak_cutoff_energy_curve_of_plateau
    (volume.restrict J) (G.horizontalFields hq) (G.horizontalFields_contDiff hq)
    hφ hk hC hL (Filter.Eventually.of_forall hb) hkb hP hφP hψ u g vψ hvψ hvalψ hgradψ
  refine ⟨v, hv, ?_, hrep, hgrad⟩
  have hrep' : ∀ᵐ t ∂volume.restrict J,
      ((v t : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) =ᵐ[
        volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
          fun x => u t x * φ x := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hrep
  have hspatial : essSup (fun t => eLpNorm (u t) 2
      ((volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict (tsupport φ)))
      (volume.restrict J) < ⊤ := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (hlocal J (tsupport φ) hJ hJI hc hs).1
  have H := essSup_eLpNorm_cutoff_rep_lt_top hc.measurableSet u hb (subset_tsupport φ)
    (fun t => (v t : GradientSpace (N := N) ⊤ q).fst) hrep' hspatial
  simpa only [Opens.coe_top, Measure.restrict_univ] using H

end HeatKernel
