-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiCylinders

/-! # Measure ratios for buffered Harnack cylinders

The logarithmic regions and the outer iteration cylinders have the same spatial
ball. Their measure ratios therefore follow from the rational time buffers on any
spatial measure space. The remaining spatial measure ratio is an explicit input
to the comparison with the earlier mean-value source.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]

/-- The earlier iteration-cylinder measure is its time length times the ball measure. -/
theorem measure_harnackEarlierIterationCylinder (ν : Measure E) [SFinite ν] (x : E) (t r σ : ℝ) :
    (volume.prod ν) (harnackEarlierIterationCylinder x t r σ) =
      ENNReal.ofReal (5 / 4 * σ ^ 2 * r ^ 2) * ν (Metric.ball x (5 / 4 * σ * r)) := by
  rw [harnackEarlierIterationCylinder, Measure.prod_prod, Real.volume_Ioo]
  congr 2
  ring

/-- The later iteration-cylinder measure is its time length times the ball measure. -/
theorem measure_harnackLaterIterationCylinder (ν : Measure E) [SFinite ν] (x : E) (t r σ : ℝ) :
    (volume.prod ν) (harnackLaterIterationCylinder x t r σ) =
      ENNReal.ofReal (3 / 2 * σ ^ 2 * r ^ 2) * ν (Metric.ball x (5 / 4 * σ * r)) := by
  rw [harnackLaterIterationCylinder, Measure.prod_prod, Real.volume_Ioo]
  congr 2
  ring

/-- The earlier logarithmic region has at most 57/40 times the outer iteration measure. -/
theorem measure_earlier_logarithmic_region_le (ν : Measure E) [SFinite ν] (x : E) (t r τ : ℝ)
    (hτ : τ < t - 111 / 64 * r ^ 2) :
    (volume.prod ν) (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ≤
      ENNReal.ofReal (57 / 40 : ℝ) *
        (volume.prod ν) (harnackEarlierIterationCylinder x t r 1) := by
  rw [Measure.prod_prod, Real.volume_Ioo, measure_harnackEarlierIterationCylinder]
  simp only [one_pow, mul_one]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 57 / 40)]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

/-- The later logarithmic region has at most 113/96 times the outer iteration measure. -/
theorem measure_later_logarithmic_region_le (ν : Measure E) [SFinite ν] (x : E) (t r τ : ℝ)
    (hτ : t - 113 / 64 * r ^ 2 < τ) :
    (volume.prod ν) (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ≤
      ENNReal.ofReal (113 / 96 : ℝ) *
        (volume.prod ν) (harnackLaterIterationCylinder x t r 1) := by
  rw [Measure.prod_prod, Real.volume_Ioo, measure_harnackLaterIterationCylinder]
  simp only [one_pow, mul_one]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 113 / 96)]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _

/-- The earlier outer-to-source measure comparison separates the exact time ratio
40/37 from the supplied spatial ball ratio. -/
theorem measure_earlier_iteration_le_source_of_ball_ratio (ν : Measure E) [SFinite ν] (x : E)
    (t r : ℝ) {K : ℝ≥0∞}
    (hballs : ν (Metric.ball x (5 / 4 * r)) ≤ K * ν (Metric.ball x (6 / 5 * r))) :
    (volume.prod ν) (harnackEarlierIterationCylinder x t r 1) ≤
      (ENNReal.ofReal (40 / 37 : ℝ) * K) *
        (volume.prod ν) (harnackEarlierSourceCylinder x t r) := by
  rw [measure_harnackEarlierIterationCylinder, harnackEarlierSourceCylinder,
    Measure.prod_prod, Real.volume_Ioo]
  simp only [one_pow, mul_one]
  have htime : 5 / 4 * r ^ 2 =
      (40 / 37 : ℝ) * ((t - 63 / 32 * r ^ 2) - (t - 25 / 8 * r ^ 2)) := by ring
  rw [htime, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40 / 37)]
  calc
    _ ≤ (ENNReal.ofReal (40 / 37 : ℝ) *
        ENNReal.ofReal ((t - 63 / 32 * r ^ 2) - (t - 25 / 8 * r ^ 2))) *
          (K * ν (Metric.ball x (6 / 5 * r))) := mul_le_mul_right hballs _
    _ = _ := by ac_rfl

end HeatKernel
