-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.StationaryLebesgueMap
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Continuous spatial test functionals from space-time L² pairings -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [SFinite ν]

/-- Pairing a fixed space-time L² function with a stationary spatial test is continuous linear. -/
def stationaryLpPairing (F : Lp ℝ 2 (μ.prod ν)) : Lp ℝ 2 ν →L[ℝ] ℝ :=
  (innerSL ℝ F).comp (stationaryLpContinuousLinearMap μ ν)

/-- The continuous pairing is the concrete space-time integral. -/
theorem stationaryLpPairing_apply (F : Lp ℝ 2 (μ.prod ν)) (v : Lp ℝ 2 ν) :
    stationaryLpPairing μ ν F v = ∫ z : α × β, F z * v z.2 ∂μ.prod ν := by
  change inner ℝ F (stationaryLp μ ν v) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stationaryLp_coeFn μ ν v] with z hz
  simp only [hz, Real.inner_apply]

end HeatKernel
