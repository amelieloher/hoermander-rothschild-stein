-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactZeroBoundary
public import HeatKernel.Form.GraphLimits
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linter

/-! # Essential compact support and zero-boundary energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped Topology

namespace HeatKernel

/-- Vanishing almost everywhere off a compact set gives a representative supported in that set. -/
theorem exists_compact_representative_of_ae_zero_off {N : ℕ} {f : (Fin N → ℝ) → ℝ}
    {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ∃ g : (Fin N → ℝ) → ℝ, HasCompactSupport g ∧ tsupport g ⊆ K ∧ f =ᵐ[volume] g := by
  let g := K.indicator f
  have hs : Function.support g ⊆ K := by
    intro x hx
    by_contra hn
    exact hx (by simp only [g, indicator_of_notMem hn])
  have ht : tsupport g ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨g, hK.of_isClosed_subset (isClosed_tsupport g) ht, ht, ?_⟩
  filter_upwards [hf] with x hx
  by_cases h : x ∈ K
  · simp only [g, indicator_of_mem h]
  · simp only [g, indicator_of_notMem h, hx h]

/-- An energy function with essential compact support inside an open set has zero boundary values. -/
theorem mem_zeroBoundaryGraph_of_ae_zero_off_compact {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : ∀ᵐ x ∂volume, x ∉ K → (u : GradientSpace (N := N) ⊤ q).fst x = 0) :
    (u : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X := by
  obtain ⟨f, hc, hs, hf⟩ := exists_compact_representative_of_ae_zero_off hK hu
  exact mem_zeroBoundaryGraph_of_compact_support U X hX u hc (hs.trans hKU) hf

end HeatKernel
