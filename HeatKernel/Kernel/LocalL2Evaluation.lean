-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.LocalEvaluation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Uniform evaluation bounds for local square-integrable representatives

The compact-space embedding into square-integrable functions provides the comparison
map for the closed graph argument. Positive measure on open sets gives injectivity.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel

variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- Local square-integrable agreement gives a uniform point-evaluation bound on a compact set. -/
theorem exists_evaluation_bound_of_localL2_representatives (L : H →ₗ[ℝ] C(X, ℝ))
    (B : H →L[ℝ] Lp ℝ 2 μ) (hrep : ∀ f, B f =ᵐ[μ] L f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f x, ‖L f x‖ ≤ C * ‖f‖ := by
  apply exists_evaluation_bound_of_injective_comparison L (ContinuousMap.toLp 2 μ ℝ) B
    (ContinuousMap.toLp_injective μ)
  intro f
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp μ (L f)).trans (hrep f).symm

end HeatKernel
