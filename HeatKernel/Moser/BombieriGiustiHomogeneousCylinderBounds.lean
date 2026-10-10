-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiHomogeneousCylinderMeasures
import Mathlib.Tactic

/-! # Positive finite measures of horizontal product cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A positive-length time interval and a positive-radius horizontal metric ball
give a positive finite spacetime cylinder measure. -/
theorem measure_horizontal_product_cylinder_pos_finite
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {a b r : ℝ} (hab : a < b) (hr : 0 < r) :
    0 < (volume.prod (CarnotPoint.volume G hq hqpos hspan))
      (Ioo a b ×ˢ Metric.ball x r) ∧
    (volume.prod (CarnotPoint.volume G hq hqpos hspan))
      (Ioo a b ×ˢ Metric.ball x r) < ⊤ := by
  let : SFinite (CarnotPoint.volume G hq hqpos hspan) := by
    change SFinite (volume : Measure (Fin N → ℝ))
    infer_instance
  have hunit := CarnotPoint.volume_unitBall_pos_finite G hq hqpos hspan hw
  rw [Measure.prod_prod, Real.volume_Ioo,
    CarnotPoint.volume_ball_of_nonneg G hq hqpos hspan hw x hr.le]
  constructor
  · exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
      (mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne' hunit.1.ne')
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hunit.2)

end HeatKernel
