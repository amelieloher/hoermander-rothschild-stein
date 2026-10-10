-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CompactNormalizedDatum
import Mathlib.Tactic

/-! # Boundedness and unit norm of normalized local data

Continuity of a row on a proper space bounds its restriction to a finite ball.
The normalized datum is essentially bounded and has Hilbert norm exactly one.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
namespace HeatKernel.Gaussian

/-- Normalizing a nonnegative row preserves pointwise nonnegativity. -/
theorem normalized_indicator_nonneg {α : Type*} (S : Set α) (f : α → ℝ)
    (hn : ∀ z, 0 ≤ f z) (A : ℝ) :
    ∀ z, 0 ≤ S.indicator (fun w ↦ f w / Real.sqrt A) z := by
  intro z
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz]
    exact div_nonneg (hn z) (Real.sqrt_nonneg _)
  · simp [hz]

end HeatKernel.Gaussian
