-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.HomogeneousPacking

/-! Volume comparison for homogeneous balls with comparable radii. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- A factor-two radius comparison gives the exact factor 2^Q in homogeneous volume,
independently of the two centers. -/
theorem measure_ball_le_two_pow_mul_of_radius_le_two_mul {E : Type*} [MetricSpace E]
    [MeasurableSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (z w : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 2 * a) :
    μ (ball w b) ≤ (2 : ℝ≥0∞) ^ Q * μ (ball z a) := by
  calc
    μ (ball w b) = ENNReal.ofReal (b ^ Q) * v := hvolume w b hb
    _ ≤ ENNReal.ofReal ((2 * a) ^ Q) * v :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hb.le hba Q)) v
    _ = (2 : ℝ≥0∞) ^ Q * μ (ball z a) := by
      rw [hvolume z a ha, mul_pow, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]

end HeatKernel
