-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocDoubling
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- The radial ball-measure function is measurable because it is monotone.
This supplies measurability for the volume-integral kernels of BB pp. 296–297. -/
theorem measurable_ball_measure (μ : Measure X) (z : X) :
    Measurable (fun r : ℝ => μ (ball z r)) := by
  have hm : Monotone (fun r : ℝ => μ (ball z r)) :=
    fun _ _ h => measure_mono (ball_subset_ball h)
  exact hm.measurable

/-- Volume at a fixed centre is a measurable function of the other point. -/
theorem measurable_volumeAt (μ : Measure X) (z : X) : Measurable (volumeAt μ z) :=
  (measurable_ball_measure μ z).comp (continuous_const.dist continuous_id).measurable

end RothschildStein.H2
