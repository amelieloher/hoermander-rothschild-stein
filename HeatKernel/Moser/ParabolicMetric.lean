-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The parabolic metric on space-time -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeatKernel

/-- Space-time with the square-root time metric and the maximum product metric. -/
abbrev ParabolicSpaceTime (X : Type*) :=
  Metric.Snowflaking ℝ (1 / 2) (by norm_num) (by norm_num) × X

/-- The parabolic metric induces the usual product topology. -/
def parabolicSpaceTimeHomeomorph (X : Type*) [TopologicalSpace X] :
    ParabolicSpaceTime X ≃ₜ ℝ × X :=
  Metric.Snowflaking.homeomorph.prodCongr (Homeomorph.refl X)

/-- Parabolic distance is the maximum of spatial distance and square-root time separation. -/
theorem parabolicSpaceTime_dist {X : Type*} [PseudoMetricSpace X]
    (z w : ParabolicSpaceTime X) :
    dist z w = max (Real.sqrt |z.1.val - w.1.val|) (dist z.2 w.2) := by
  change max (dist z.1 w.1) (dist z.2 w.2) = _
  congr 1
  change (dist z.1.val w.1.val) ^ (1 / (2 : ℝ)) = _
  rw [Real.dist_eq, Real.sqrt_eq_rpow]

end HeatKernel
