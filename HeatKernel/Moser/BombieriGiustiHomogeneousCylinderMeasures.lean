-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiCylinderMeasures
public import HeatKernel.Geometry.MetricBallVolume

/-! # Homogeneous spatial measure ratios in the Harnack bridge

The homogeneous ball-volume formula discharges the spatial measure ratio between
the earlier outer iteration cylinder and its mean-value source. The resulting
constant depends only on the homogeneous dimension.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel

variable {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)

include hw

/-- The spatial balls in the earlier bridge have the fixed homogeneous volume ratio. -/
theorem measure_harnackEarlier_ball_ratio (x : CarnotPoint G hq hqpos hspan)
    {r : ℝ} (hr : 0 ≤ r) :
    CarnotPoint.volume G hq hqpos hspan (Metric.ball x (5 / 4 * r)) =
      ENNReal.ofReal ((25 / 24 : ℝ) ^ G.homogeneousDimension) *
        CarnotPoint.volume G hq hqpos hspan (Metric.ball x (6 / 5 * r)) := by
  rw [CarnotPoint.volume_ball_of_nonneg G hq hqpos hspan hw x (by positivity),
    CarnotPoint.volume_ball_of_nonneg G hq hqpos hspan hw x (by positivity)]
  have he : (5 / 4 * r) ^ G.homogeneousDimension =
      (25 / 24 : ℝ) ^ G.homogeneousDimension * (6 / 5 * r) ^ G.homogeneousDimension := by
    rw [← mul_pow]
    congr 1
    ring
  rw [he, ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- The earlier outer iteration measure is controlled by the source measure with
the fixed factor `(40/37) (25/24)^Q`. No solution-dependent geometric input remains. -/
theorem measure_harnackEarlier_iteration_le_source
    (x : CarnotPoint G hq hqpos hspan) (t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (volume.prod (CarnotPoint.volume G hq hqpos hspan))
        (harnackEarlierIterationCylinder x t r 1) ≤
      ENNReal.ofReal ((40 / 37 : ℝ) * (25 / 24 : ℝ) ^ G.homogeneousDimension) *
        (volume.prod (CarnotPoint.volume G hq hqpos hspan))
          (harnackEarlierSourceCylinder x t r) := by
  let : SFinite (CarnotPoint.volume G hq hqpos hspan) := by
    change SFinite (volume : Measure (Fin N → ℝ))
    infer_instance
  have h := measure_earlier_iteration_le_source_of_ball_ratio
    (CarnotPoint.volume G hq hqpos hspan) x t r
    (measure_harnackEarlier_ball_ratio G hq hqpos hspan hw x hr).le
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40 / 37)] using h

end HeatKernel
