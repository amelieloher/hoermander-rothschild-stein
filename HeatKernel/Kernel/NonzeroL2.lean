-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactEvaluation
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # A nonzero vector in Euclidean Lebesgue L²

The unit closed ball has finite positive measure. Its indicator supplies the
nonzero L² input needed to exclude zero mass by strong continuity.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Euclidean Lebesgue L² contains a nonzero vector, including in dimension zero. -/
theorem exists_nonzero_euclidean_L2 (n : ℕ) :
    ∃ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)), f ≠ 0 := by
  let K := Metric.closedBall (0 : Fin n → ℝ) 1
  have hfinite : volume K ≠ ⊤ := (isCompact_closedBall (0 : Fin n → ℝ) 1).measure_lt_top.ne
  have hpositive : 0 < volume K := Metric.measure_closedBall_pos volume 0 (by norm_num)
  have hreal : 0 < volume.real K := ENNReal.toReal_pos hpositive.ne' hfinite
  let f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
    indicatorConstLp 2 (s := K) measurableSet_closedBall hfinite (1 : ℝ)
  refine ⟨f, ?_⟩
  have hnorm : 0 < ‖f‖ := by
    change 0 < ‖indicatorConstLp 2 (s := K) measurableSet_closedBall hfinite (1 : ℝ)‖
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos hreal _
  exact norm_ne_zero_iff.mp (ne_of_gt hnorm)

end HeatKernel
