-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactZeroBoundary
public import HeatKernel.Form.ZeroBoundaryCore
public import HeatKernel.Form.ContractionGraphNorm
public import HeatKernel.Form.ClosedConvexLift
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linter

/-! # Normal contractions preserve zero-boundary energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

namespace HeatKernel

/-- Normal scalar contractions preserve the zero-boundary graph on every open set. -/
theorem exists_zeroBoundaryGraph_comp_normalContraction {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : zeroBoundaryGraph U X)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X ∧
      energyInclusion ⊤ X z = hη.compLp hzero (v : GradientSpace (N := N) ⊤ q).fst := by
  obtain ⟨w, hw, ht⟩ := exists_interiorGradientPairs_tendsto U X v
  let e : ℕ → energyGraph (N := N) ⊤ X := fun n =>
    ⟨w n, zeroBoundaryGraph_le_energyGraph U X
      (interiorGradientPairs_subset_zeroBoundaryGraph U X (hw n))⟩
  choose z hz hznorm using fun n => exists_energyGraph_comp_normalContraction_norm_le X hX (e n) hη hzero
  have hmem : ∀ n, (z n : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X := by
    intro n
    obtain ⟨f, hf, hc, hs, hrf, _⟩ := hw n
    have hrep : (z n : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] η ∘ f := by
      have H := hη.coeFn_compLp hzero (energyInclusion ⊤ X (e n))
      rw [← hz n] at H
      change (z n : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict
        ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))]
        η ∘ (e n : GradientSpace (N := N) ⊤ q).fst at H
      have H' : (z n : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
          η ∘ (w n).fst := by
        simpa only [e, Opens.coe_top, Measure.restrict_univ] using H
      exact H'.trans (hrf.fun_comp η)
    exact mem_zeroBoundaryGraph_of_compact_support U X hX (z n)
      (hc.comp_left hzero) ((tsupport_comp_subset hzero f).trans hs) hrep
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto w ht).exists_norm_le
  have hb : ∀ n, ‖z n‖ ≤ M := fun n => (hznorm n).trans (hM _ (mem_range_self n))
  have hlim : Tendsto (fun n => energyInclusion ⊤ X (z n)) atTop
      (𝓝 (hη.compLp hzero (v : GradientSpace (N := N) ⊤ q).fst)) := by
    have H := (hη.continuous_compLp hzero).continuousAt.tendsto.comp
      ((tendsto_GradientSpace_iff ⊤).mp ht).1
    exact H.congr (fun n => (hz n).symm)
  let C : Set (energyGraph (N := N) ⊤ X) :=
    (fun u => (u : GradientSpace (N := N) ⊤ q)) ⁻¹' (zeroBoundaryGraph U X : Set _)
  have hC : Convex ℝ C := (zeroBoundaryGraph U X).convex.linear_preimage (energyGraph ⊤ X).subtype
  have hc : IsClosed C := (isClosed_zeroBoundaryGraph U X).preimage continuous_subtype_val
  let : InnerProductSpace ℝ (energyGraph (N := N) ⊤ X) :=
    { (inferInstance : InnerProductSpace ℝ (energyGraph (N := N) ⊤ X)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (energyGraph (N := N) ⊤ X)) }
  let : InnerProductSpace ℝ (SpatialL2 (⊤ : Opens (Fin N → ℝ))) :=
    { (inferInstance : InnerProductSpace ℝ (SpatialL2 (⊤ : Opens (Fin N → ℝ)))) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (SpatialL2 (⊤ : Opens (Fin N → ℝ)))) }
  obtain ⟨u, hu, _, huc⟩ := exists_lift_of_tendsto_of_bounded_mem_closed_convex
    (energyInclusion ⊤ X) z hb hC hc hmem hlim
  exact ⟨u, huc, hu⟩



end HeatKernel
