-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMeanPrimitive

/-! Two-sided time integration of logarithmic energy majorants. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace HeatKernel

/-- The reciprocal primitive has absolute integral at most the inverse threshold. -/
theorem abs_integral_deriv_div_shift_sq_le {q : ℝ → ℝ} {a b c : ℝ}
    (hc : 0 < c) (hq : AbsolutelyContinuousOnInterval q a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ q t) :
    |∫ t in a..b, deriv q t / (c + q t)^2| ≤ c⁻¹ := by
  rw [integral_deriv_div_shift_sq hc hq hn, abs_le]
  have ha : c ≤ c + q a := by linarith [hn a left_mem_uIcc]
  have hb : c ≤ c + q b := by linarith [hn b right_mem_uIcc]
  have hia : (c + q a)⁻¹ ≤ c⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hc ha
  have hib : (c + q b)⁻¹ ≤ c⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hc hb
  have hna := inv_nonneg.mpr (hc.le.trans ha)
  have hnb := inv_nonneg.mpr (hc.le.trans hb)
  constructor <;> linarith

/-- Either sign of an absolutely continuous mean deviation gives the same integrated
energy tail bound. The sign parameter covers earlier and later separating-time tails. -/
theorem integral_energy_div_shift_sq_le {q E : ℝ → ℝ} {a b c σ : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hσ : |σ| ≤ 1)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ q t)
    (hE : IntervalIntegrable E volume a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * σ * deriv q t) :
    (∫ t in a..b, E t / (c + q t)^2) ≤ 2 / c := by
  have hw : ContinuousOn (fun t => 1 / (c + q t)^2) (uIcc a b) :=
    continuousOn_const.div ((continuousOn_const.add hq.continuousOn).pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (by linarith [hn t ht])))
  have hi : IntervalIntegrable (fun t => E t / (c + q t)^2) volume a b := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hE.continuousOn_mul hw
  have hd : IntervalIntegrable (fun t => deriv q t / (c + q t)^2) volume a b := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hq.intervalIntegrable_deriv.continuousOn_mul hw
  have hle := intervalIntegral.integral_mono_ae_restrict hab hi (hd.const_mul (2 * σ))
    (show (fun t => E t / (c + q t)^2) ≤ᵐ[volume.restrict (Icc a b)]
      (fun t => (2 * σ) * (deriv q t / (c + q t)^2)) from by
      filter_upwards [ae_restrict_of_ae hbound, ae_restrict_mem measurableSet_Icc] with t ht hm
      have hu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hm
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (ht hu) (sq_nonneg (c + q t)))
  rw [intervalIntegral.integral_const_mul] at hle
  have hval := abs_integral_deriv_div_shift_sq_le hc hq hn
  have hmul : σ * (∫ t in a..b, deriv q t / (c + q t)^2) ≤ c⁻¹ := by
    calc
      _ ≤ |σ * (∫ t in a..b, deriv q t / (c + q t)^2)| := le_abs_self _
      _ = |σ| * |∫ t in a..b, deriv q t / (c + q t)^2| := abs_mul _ _
      _ ≤ 1 * c⁻¹ := mul_le_mul hσ hval (abs_nonneg _) (by norm_num)
      _ = c⁻¹ := one_mul _
  have hlast : (2 * σ) * (∫ t in a..b, deriv q t / (c + q t)^2) ≤ 2 / c := by
    rw [div_eq_mul_inv]
    nlinarith
  exact hle.trans hlast

end HeatKernel
