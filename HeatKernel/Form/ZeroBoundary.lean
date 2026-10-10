-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphLimits
import Mathlib.Tactic.Linter

/-! # Zero-boundary horizontal graph domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Global gradient pairs of smooth functions supported compactly inside an open set. -/
def interiorGradientPairs : Set (GradientSpace (N := N) ⊤ q) :=
  {v | ∃ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
    tsupport f ⊆ (U : Set (Fin N → ℝ)) ∧ v.fst =ᵐ[volume] f ∧
    ∀ i, v.snd i =ᵐ[volume] RothschildStein.fieldDerivative (X i) f}

/-- Closure of the interior smooth core in the global horizontal graph norm. -/
def zeroBoundaryGraph : Submodule ℝ (GradientSpace (N := N) ⊤ q) :=
  (Submodule.span ℝ (interiorGradientPairs U X)).topologicalClosure

/-- The zero-boundary graph is norm closed. -/
theorem isClosed_zeroBoundaryGraph : IsClosed (zeroBoundaryGraph U X : Set (GradientSpace (N := N) ⊤ q)) :=
  Submodule.isClosed_topologicalClosure _

/-- The zero-boundary graph is a complete Hilbert subspace of the global graph product. -/
instance : CompleteSpace (zeroBoundaryGraph U X) := (isClosed_zeroBoundaryGraph U X).completeSpace_coe

/-- Every zero-boundary graph vector belongs to the global energy domain. -/
theorem zeroBoundaryGraph_le_energyGraph : zeroBoundaryGraph U X ≤ energyGraph ⊤ X := by
  apply Submodule.topologicalClosure_minimal _ _ (isClosed_energyGraph ⊤ X)
  apply Submodule.span_le.mpr
  rintro v ⟨f, hf, hc, _, hvf, hvg⟩
  apply smoothGradientSpan_le_energyGraph ⊤ X
  apply Submodule.subset_span
  refine ⟨f, hf, hc, subset_univ _, ?_, fun i => ?_⟩
  · simpa only [Opens.coe_top, Measure.restrict_univ] using hvf
  · simpa only [Opens.coe_top, Measure.restrict_univ] using hvg i

/-- Smooth pairs supported inside the open set belong to its zero-boundary closure. -/
theorem interiorGradientPairs_subset_zeroBoundaryGraph :
    interiorGradientPairs U X ⊆ zeroBoundaryGraph U X :=
  fun _ hv => Submodule.le_topologicalClosure _ (Submodule.subset_span hv)

end HeatKernel
