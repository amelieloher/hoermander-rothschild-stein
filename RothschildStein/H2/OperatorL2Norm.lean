-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The L² operator norm in the extended-norm form used by
the all-exponent estimate (BB p. 326). -/
theorem operator_l2_eLpNorm_le (μ : Measure X) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    {cT : ℝ} (hcT : ‖T‖ ≤ cT) (v : Lp ℝ 2 μ) :
    eLpNorm (fun x => (T v) x) 2 μ ≤ ENNReal.ofReal cT * eLpNorm v 2 μ := by
  have hnorm : ‖T v‖ ≤ cT * ‖v‖ := (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hcT (norm_nonneg v))
  have he : ENNReal.ofReal ‖T v‖ ≤ ENNReal.ofReal cT * ENNReal.ofReal ‖v‖ := by
    rw [← ENNReal.ofReal_mul (by exact (norm_nonneg T).trans hcT)]
    exact ENNReal.ofReal_le_ofReal hnorm
  simpa only [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)] using he

end RothschildStein.H2
