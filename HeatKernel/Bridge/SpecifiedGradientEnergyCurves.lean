-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ParabolicEnergyCurves
import Mathlib.Tactic.Linter

/-! # Cutoff energy curves for a specified local weak gradient -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Every supplied weak gradient with the local parabolic energy bounds yields
Bochner cutoff curves whose horizontal gradients use that same representative. -/
theorem IsLocalWeakSolution.exists_cutoff_energy_curves_of_weak_gradient {N q : ℕ}
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
        (∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          fun x => u t x * φ x) ∧
        ∀ i, ∀ᵐ t ∂volume.restrict J, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
          fun x => g i t x * φ x + u t x * fieldDerivative (G.horizontalFields hq i) φ x := by
  obtain ⟨hum, _, _, _, _⟩ := hu
  intro J hJ hJI φ hφ hc hs
  obtain ⟨W, hφW, hWc, hWU⟩ := exists_precompact_open_of_isCompact U hc hs
  let K : Set (Fin N → ℝ) := closure (W : Set (Fin N → ℝ))
  have hWK : (W : Set (Fin N → ℝ)) ⊆ K := subset_closure
  let : IsFiniteMeasure (volume.restrict J) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hJ.measure_lt_top⟩
  have humJK : AEStronglyMeasurable (Function.uncurry u)
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hum.mono_measure (Measure.restrict_mono (prod_mono hJI hWU) le_rfl)
  have huJK := memLp_product_of_essSup_spatial_eLpNorm_lt_top humJK
    (hlocal J K hJ hJI hWc hWU).1
  have hmeasure : (volume.restrict J).prod (volume.restrict (W : Set (Fin N → ℝ))) ≤
      (volume.restrict J).prod (volume.restrict K) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono hWK le_rfl)
  have huW := huJK.mono_measure hmeasure
  have hgW : ∀ i, MemLp (Function.uncurry (g i)) 2
      ((volume.restrict J).prod (volume.restrict (W : Set (Fin N → ℝ)))) := by
    intro i
    have H : MemLp (Function.uncurry (g i)) 2 ((volume.restrict J).prod (volume.restrict K)) := by
      simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod, Function.uncurry_def] using
        (hlocal J K hJ hJI hWc hWU).2 i
    exact H.mono_measure hmeasure
  have hwJ : ∀ᵐ t ∂volume.restrict J, ∀ i,
      hasWeakWordDeriv (G.horizontalFields hq) W [i] (u t) (g i t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hweak] with t ht
    exact fun i => S.hasWeakWordDeriv_restrict _ U W (subset_closure.trans hWU) (ht i)
  exact exists_cutoff_energyGraph_curve W (G.horizontalFields hq) (G.horizontalFields_contDiff hq)
    u g huW hgW hwJ hφ hc hφW

end HeatKernel
