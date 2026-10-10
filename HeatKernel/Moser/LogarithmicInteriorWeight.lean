-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Interior lower bounds for logarithmic squared-tent weights -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
namespace HeatKernel

/-- The squared distance tent is at least one eighty-first on the ball of radius
eight ninths of its support radius. -/
theorem logarithmic_tent_sq_lower_bound_on_inner_ball
    {X : Type*} [PseudoMetricSpace X] (x : X) {r : ℝ} (hr : 0 < r)
    {y : X} (hy : y ∈ ball x (8 * r / 9)) :
    (1 : ℝ) / 81 ≤ max (1 - dist x y / r) 0 ^ 2 := by
  have hd : dist x y < 8 * r / 9 := by
    simpa only [mem_ball, dist_comm y x] using hy
  have hdiv : dist x y / r < 8 / 9 :=
    (div_lt_iff₀ hr).mpr (by nlinarith)
  have hm := le_max_left (1 - dist x y / r) 0
  have hn := le_max_right (1 - dist x y / r) 0
  nlinarith

end HeatKernel
