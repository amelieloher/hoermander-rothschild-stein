-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.VolumeIntegrals
public import RothschildStein.H2.LocalAverage
public import RothschildStein.H2.VolumeMeasurability
public import RothschildStein.H2.LpBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Positive geometric-series denominator and near coefficient. -/
theorem hedbergVolumeIntegralConstant_pos {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) :
    0 < volumeIntegralConstant C ν := by
  apply div_pos hC
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

end RothschildStein.H2
