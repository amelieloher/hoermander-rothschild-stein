-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SmoothComposition
public import HeatKernel.Form.BoundedCoefficientLimits
public import HeatKernel.Form.GraphLimits
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Smooth scalar composition in the closed energy domain

Smooth scalar functions vanishing at zero, with bounded derivative, act on the closed
horizontal energy graph. The horizontal derivative is the pointwise scalar derivative times
the original horizontal derivative.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace HeatKernel

/-- A bounded measurable scalar coefficient preserves L². -/
theorem memLp_mul_of_ae_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a g : α → ℝ} {C : ℝ} (ha : AEStronglyMeasurable a μ) (hg : MemLp g 2 μ)
    (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    MemLp (fun x => a x * g x) 2 μ := by
  apply (hg.const_mul C).of_le (ha.mul hg.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  simpa only [Pi.mul_apply, norm_mul, Real.norm_of_nonneg hC] using
    mul_le_mul_of_nonneg_right hx (norm_nonneg (g x))

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    {η : ℝ → ℝ} {k : ℝ≥0} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hLip : LipschitzWith k η) (hzero : η 0 = 0) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ s, ‖deriv η s‖ ≤ C)

end HeatKernel
