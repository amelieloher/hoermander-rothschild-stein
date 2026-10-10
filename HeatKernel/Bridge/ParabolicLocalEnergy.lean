-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompactTimeSlices
public import RothschildStein.H3.RelcompactOpenExhaustion
import Mathlib.Tactic.Linter

/-! # Local horizontal form representatives of parabolic weak solutions -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Compact-cylinder bounds and a countable spatial exhaustion give local
horizontal Sobolev membership for almost every time slice. -/
theorem IsLocalWeakSolution.exists_local_sobolev_slices {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) :
    ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i,
        hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t)) ∧
      ∀ᵐ t ∂(volume.restrict (I : Set ℝ)),
        memSobolevXLoc noDriftWeight (G.horizontalFields hq) U 1 2 (u t) := by
  obtain ⟨g, hg, hcompact⟩ := hu.exists_square_integrable_compact_slices G hq hqpos hw hspan a I U
  obtain ⟨V, _, hV, _, hcofinal⟩ := H3.exists_relcompact_open_exhaustion U
  have hslice : ∀ n, ∀ᵐ t ∂(volume.restrict (I : Set ℝ)),
      MemLp (u t) 2 (volume.restrict (closure (V n : Set (Fin N → ℝ)))) ∧
      ∀ i, MemLp (g i t) 2 (volume.restrict (closure (V n : Set (Fin N → ℝ)))) := by
    intro n
    exact hcompact _ (hV n).1 ((hV n).2.1.trans (hV (n + 1)).2.2)
  refine ⟨g, hg, ?_⟩
  have hall := (ae_all_iff).mpr hslice
  filter_upwards [hg, hall] with t hgt hct
  intro W hWc hWU
  obtain ⟨n, hn⟩ := hcofinal _ hWc hWU
  have hsub : (W : Set (Fin N → ℝ)) ⊆ closure (V n : Set (Fin N → ℝ)) :=
    subset_closure.trans (hn.trans subset_closure)
  have hmeasure := Measure.restrict_mono hsub (le_refl (volume : Measure (Fin N → ℝ)))
  apply memSobolevX_noDrift_one_two_iff.mpr
  refine ⟨MemLp.mono_measure hmeasure (hct n).1, fun i => ?_⟩
  exact ⟨g i t, S.hasWeakWordDeriv_restrict (G.horizontalFields hq) U W
    (subset_closure.trans hWU) (hgt i), MemLp.mono_measure hmeasure ((hct n).2 i)⟩

/-- The literal parabolic weak predicate supplies local form representatives on
almost every time slice, with its own gradient as their horizontal gradient. -/
theorem IsLocalWeakSolution.exists_local_energy_slices {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) :
    ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i,
        hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t)) ∧
      ∀ᵐ t ∂(volume.restrict (I : Set ℝ)),
        MemLocalEnergy U (G.horizontalFields hq) (u t) ∧
        ∀ V : Opens (Fin N → ℝ), IsCompact (closure (V : Set (Fin N → ℝ))) →
          closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) →
          ∃ w : energyGraph (N := N) ⊤ (G.horizontalFields hq),
            (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] u t ∧
            ∀ i, energyGradient ⊤ (G.horizontalFields hq) w i =ᵐ[
              volume.restrict (V : Set (Fin N → ℝ))] g i t := by
  obtain ⟨g, hg, hs⟩ := hu.exists_local_sobolev_slices G hq hqpos hw hspan a I U
  exact ⟨g, hg, ae_exists_local_energy_representatives_of_slice_sobolev I U
    (G.horizontalFields hq) (G.horizontalFields_contDiff hq) hs hg⟩

end HeatKernel
