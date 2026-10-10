-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualPrecomposition
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Integrating weak equations in continuous dual spaces -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Bounded scalar multiplication of a dual-valued L² curve is integrable
 on a finite measure space. -/
theorem integrable_bounded_smul_dual_of_memLp_two {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} [IsFiniteMeasure μ]
    {χ : α → ℝ} (hχ : MemLp χ ⊤ μ) {D : α → (E →L[ℝ] ℝ)} (hD : MemLp D 2 μ) :
    Integrable (fun t => χ t • D t) μ := by
  have hp : MemLp (χ • D) 2 μ := hχ.smul hD
  exact hp.integrable (by norm_num)

/-- Equality of all scalar evaluations upgrades an integrated weak equation
 to an equality of Bochner integrals in the continuous dual. -/
theorem integral_smul_dual_eq_of_eval {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    {χ ψ : α → ℝ} {D F : α → (E →L[ℝ] ℝ)}
    (hD : Integrable (fun t => χ t • D t) μ)
    (hF : Integrable (fun t => ψ t • F t) μ)
    (hbalance : ∀ v : E, (∫ t, χ t * D t v ∂μ) = ∫ t, ψ t * F t v ∂μ) :
    (∫ t, χ t • D t ∂μ) = ∫ t, ψ t • F t ∂μ := by
  ext v
  rw [ContinuousLinearMap.integral_apply hD v, ContinuousLinearMap.integral_apply hF v]
  simpa only [smul_apply, smul_eq_mul] using hbalance v

end HeatKernel
