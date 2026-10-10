-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CarnotLowerBound
public import HeatKernel.Gaussian.CommonConstants
import Mathlib.Tactic

/-! # Homogeneous time normalization of Gaussian estimates

The reciprocal horizontal heat-ball volume equals the unit-volume factor times
the homogeneous time power. Absorbing the fixed unit volume into the constants
preserves one positive ordered pair and the literal control-distance exponent.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
namespace HeatKernel.Gaussian

/-- The reciprocal heat-ball volume has exactly the homogeneous time exponent. -/
theorem inv_carnot_heat_volume_eq {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {t : ℝ} (ht : 0 < t) :
    ((CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t)))⁻¹ =
      (volume.real (horizontalBall (G.horizontalFields hq) 0 1))⁻¹ *
        t ^ (-(G.homogeneousDimension : ℝ) / 2) := by
  rw [CarnotPoint.volumeReal_ball G hq hqpos hspan hw x (Real.sqrt_pos.mpr ht), mul_inv,
    ← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le]
  congr 2
  ring

/-- Multiplying the homogeneous time power by a constant is equivalent to
using its unit-volume multiple over the heat-ball volume. -/
theorem mul_time_power_eq_unit_volume_div_heat_volume {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (a : ℝ) (x : CarnotPoint G hq hqpos hspan) {t : ℝ} (ht : 0 < t) :
    a * t ^ (-(G.homogeneousDimension : ℝ) / 2) =
      (a * volume.real (horizontalBall (G.horizontalFields hq) 0 1)) /
        (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t)) := by
  have hv := horizontal_unit_ball_volume_real_pos G hq hqpos hspan hw
  simp only [div_eq_mul_inv]
  rw [inv_carnot_heat_volume_eq G hq hqpos hspan hw x ht]
  field_simp [hv.ne']

end HeatKernel.Gaussian
