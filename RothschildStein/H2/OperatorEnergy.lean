-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Express the L² square seminorm as the square integral. -/
theorem l2_square_integral_eq (μ : Measure X) {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) = eLpNorm f 2 μ ^ 2 := by
  simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf).symm

/-- The bounded L² operator multiplies square integrals by at
most the square of its norm bound (BB pp. 319–320). -/
theorem operator_square_integral_le (μ : Measure X)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {cT : ℝ} (hcT : ‖T‖ ≤ cT) (v : Lp ℝ 2 μ) :
    (∫⁻ x, ‖(T v) x‖ₑ ^ 2 ∂μ) ≤
      ENNReal.ofReal cT ^ 2 * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ := by
  have hc : 0 ≤ cT := (norm_nonneg T).trans hcT
  have hn : eLpNorm (T v) 2 μ ≤ ENNReal.ofReal cT * eLpNorm v 2 μ := by
    rw [← Lp.enorm_def, ← Lp.enorm_def]
    calc
      _ ≤ ENNReal.ofReal (cT * ‖v‖) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((T.le_opNorm v).trans
          (mul_le_mul_of_nonneg_right hcT (norm_nonneg v)))
      _ = _ := by rw [ENNReal.ofReal_mul hc, ofReal_norm]
  rw [l2_square_integral_eq μ (Lp.aestronglyMeasurable (T v)),
    l2_square_integral_eq μ (Lp.aestronglyMeasurable v), ← mul_pow]
  gcongr

end RothschildStein.H2
