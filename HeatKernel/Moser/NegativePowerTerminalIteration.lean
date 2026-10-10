-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerEnergyFactors
public import HeatKernel.Moser.NegativePowerFiniteIteration
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Reciprocal iteration from nested terminal energy budgets -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A positive lower bound on a finite-measure region supplies every finite
reciprocal moment needed to start the iteration. -/
theorem memLp_reciprocal_of_positive_lower_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hu : AEStronglyMeasurable u μ)
    (hlower : ∀ᵐ x ∂μ, ε ≤ u x) (p : ℝ≥0∞) :
    MemLp (fun x => (u x)⁻¹) p μ := by
  apply MemLp.of_bound hu.aemeasurable.inv.aestronglyMeasurable ε⁻¹
  filter_upwards [hlower] with x hx
  change ‖(u x)⁻¹‖ ≤ ε⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hε.trans_le hx))]
  exact inv_anti₀ hε hx

end HeatKernel
