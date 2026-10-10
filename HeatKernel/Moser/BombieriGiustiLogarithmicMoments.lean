-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiFiniteMoments

/-! # Logarithmic coordinates of finite moment norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A scaled positive moment bound yields the corresponding logarithmic norm
bound, including when the moment or the bounded quantity is zero. -/
theorem nonnegativeLogSupremum_le_of_scaled_moment {s m : ℝ≥0∞} {p D : ℝ}
    (hp : 0 < p) (hm : m ≠ ⊤)
    (hbound : s ≤ ENNReal.ofReal (Real.exp D) * m ^ (1 / p)) :
    nonnegativeLogSupremum s ≤ max 0 (D + Real.log m.toReal / p) := by
  by_cases hs : s = 0
  · simp only [hs, nonnegativeLogSupremum, ENNReal.toReal_zero, Real.log_zero, max_self]
    exact le_max_left _ _
  have hm0 : m ≠ 0 := by
    intro hz
    simp only [hz, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp), mul_zero] at hbound
    exact hs (le_zero_iff.mp hbound)
  have hb : ENNReal.ofReal (Real.exp D) * m ^ (1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp.le) hm)
  have hsfin := ne_top_of_le_ne_top hb hbound
  have ht := ENNReal.toReal_mono hb hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos D).le,
    ← ENNReal.toReal_rpow] at ht
  have hmpos := ENNReal.toReal_pos hm0 hm
  have hl := Real.log_le_log (ENNReal.toReal_pos hs hsfin) ht
  rw [Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos hmpos _).ne',
    Real.log_exp, Real.log_rpow hmpos] at hl
  apply max_le_max_left
  convert hl using 1
  ring

/-- The logarithmic coordinate of a finite positive-exponent moment norm bounds
the original moment by its correctly scaled exponential. -/
theorem le_exp_mul_nonnegativeLogSupremum_rpow {m : ℝ≥0∞} (hm : m ≠ ⊤)
    {p : ℝ} (hp : 0 < p) :
    m ≤ ENNReal.ofReal (Real.exp (p * nonnegativeLogSupremum (m ^ (1 / p)))) := by
  have hc := le_exp_nonnegativeLogSupremum
    (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp.le) hm)
  have he := ENNReal.rpow_le_rpow hc hp.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul] at he
  simpa only [mul_comm] using he

end HeatKernel
