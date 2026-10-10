-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CompactNormalizedDatum
public import HeatKernel.Gaussian.BoundedNormalizedDatum
public import HeatKernel.Gaussian.KernelIntegralContinuity
import Mathlib.Tactic

/-! # Kernel evolutions of normalized rows

The literal kernel integral of a normalized row is nonnegative for a
nonnegative kernel, recovers its local square norm at the central point, and
is jointly continuous when the kernel is jointly continuous.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric RothschildStein
namespace HeatKernel.Gaussian

/-- The normalized kernel evolution at its central point equals the square
root of the local row square integral. -/
theorem integral_kernel_normalized_row_eq_sqrt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (p : ℝ → X → X → ℝ) (s : ℝ) (y : X)
    (hpos : 0 < ∫ z in S, p s y z ^ 2 ∂μ) :
    (∫ z, p s y z * S.indicator (fun w ↦ p s y w /
      Real.sqrt (∫ a in S, p s y a ^ 2 ∂μ)) z ∂μ) =
        Real.sqrt (∫ z in S, p s y z ^ 2 ∂μ) :=
  integral_mul_normalized_indicator_eq_sqrt μ hS (p s y) hpos

/-- A nonnegative kernel preserves nonnegativity of normalized row data
in its literal integral evolution. -/
theorem integral_kernel_normalized_row_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (p : ℝ → X → X → ℝ)
    (hn : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) (x y : X) :
    0 ≤ ∫ z, p σ x z * S.indicator (fun w ↦ p s y w /
      Real.sqrt (∫ a in S, p s y a ^ 2 ∂μ)) z ∂μ := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (hn σ hσ x z)
    (normalized_indicator_nonneg S (p s y) (hn s hs y) _ z)

end HeatKernel.Gaussian
