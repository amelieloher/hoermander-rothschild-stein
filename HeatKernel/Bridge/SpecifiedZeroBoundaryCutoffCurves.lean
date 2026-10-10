-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.BoundedCutoffEnergyCurves
public import HeatKernel.Bridge.ZeroBoundaryCutoffIdentity
public import HeatKernel.Bridge.ZeroBoundaryCutoffRepresentatives
import Mathlib.Tactic.Linter

/-! # Zero-boundary cutoff curves for a specified weak gradient -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Every specified weak gradient with local energy bounds supplies bounded
zero-boundary cutoff curves on all compact interior time sets. -/
theorem IsLocalWeakSolution.hasZeroBoundaryCutoffEnergyCurves_of_weak_gradient {N q : ℕ}
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
    (hb : HasLocalParabolicEnergyBounds I U u g) :
    HasZeroBoundaryCutoffEnergyCurves (G.horizontalFields hq) I U u g := by
  intro J hJ hJI V φ hφ hc hsU hsV
  obtain ⟨v, hv, hvb, hvf, hvg⟩ :=
    hu.exists_bounded_cutoff_energy_curves_of_weak_gradient G hq hqpos hw hspan a I U u g
      hg hb J hJ hJI φ hφ hc hsU
  obtain ⟨w, hw, he⟩ := exists_zeroBoundary_cutoff_curve V (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) v hv hc hsV hvf
  refine ⟨w, hw, ?_, ?_, fun i => ?_⟩
  · have heq : (fun t => eLpNorm ((w t : GradientSpace (N := N) ⊤ q).fst) 2 volume)
        =ᵐ[volume.restrict J]
        (fun t => eLpNorm ((v t : GradientSpace (N := N) ⊤ q).fst) 2 volume) := by
      filter_upwards [he] with t ht
      rw [ht]
    rw [essSup_congr_ae heq]
    exact hvb
  · filter_upwards [he, hvf] with t ht hf
    simpa only [ht] using hf
  · filter_upwards [he, hvg i] with t ht hi
    simpa only [ht] using hi

end HeatKernel
