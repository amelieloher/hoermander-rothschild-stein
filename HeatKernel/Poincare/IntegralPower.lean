-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MeanOscillation

/-! The finite-measure power estimate for an integral, including exponent one. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set

namespace HeatKernel

/-- Jensen gives the integral power bound with the exact measure factor, including
exponent one without a conjugate-exponent argument. -/
theorem abs_integral_rpow_le_measure_rpow_mul_integral {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] [NeZero μ] {f : E → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hf : Integrable f μ)
    (hfp : Integrable (fun x => |f x| ^ p) μ) :
    |∫ x, f x ∂μ| ^ p ≤ (μ.real univ) ^ (p - 1) * ∫ x, |f x| ^ p ∂μ := by
  have hm : 0 < μ.real univ := by
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) (measure_ne_top μ univ)
  have hid := measure_smul_average (μ := μ) (f := f)
  rw [smul_eq_mul] at hid
  rw [← hid, abs_mul, abs_of_pos hm, Real.mul_rpow hm.le (abs_nonneg _)]
  calc
    (μ.real univ) ^ p * |⨍ x, f x ∂μ| ^ p ≤
        (μ.real univ) ^ p * (⨍ x, |f x| ^ p ∂μ) :=
      mul_le_mul_of_nonneg_left (abs_average_rpow_le_average_abs_rpow hp hf hfp)
        (Real.rpow_nonneg hm.le p)
    _ = (μ.real univ) ^ (p - 1) * ∫ x, |f x| ^ p ∂μ := by
      rw [average_eq, smul_eq_mul, Real.rpow_sub hm, Real.rpow_one, div_eq_mul_inv]
      ring

end HeatKernel
