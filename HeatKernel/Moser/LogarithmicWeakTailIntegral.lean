-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicDeviationIntegral

/-! Integration of spatial logarithmic tail bounds and extension to small levels. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace HeatKernel

/-- A spatial quadratic tail estimate and either signed mean-energy inequality give
an integrated weak-L¹ bound with the numerical factor four. -/
theorem integral_logarithmic_tail_majorant_le {q E B : ℝ → ℝ} {a b ℓ K σ : ℝ}
    (hab : a ≤ b) (hℓ : 0 < ℓ) (hK : 0 ≤ K) (hσ : |σ| ≤ 1)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ q t)
    (hE : IntervalIntegrable E volume a b) (hB : IntervalIntegrable B volume a b)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * σ * deriv q t)
    (hb : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      B t ≤ K * (E t / (ℓ / 2 + q t)^2)) :
    (∫ t in a..b, B t) ≤ 4 * K / ℓ := by
  have hc : 0 < ℓ / 2 := by positivity
  have hw : ContinuousOn (fun t => 1 / (ℓ / 2 + q t)^2) (uIcc a b) :=
    continuousOn_const.div ((continuousOn_const.add hq.continuousOn).pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (by linarith [hn t ht])))
  have hi : IntervalIntegrable (fun t => E t / (ℓ / 2 + q t)^2) volume a b := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      hE.continuousOn_mul hw
  have H := intervalIntegral.integral_mono_ae_restrict hab hB (hi.const_mul K)
    (show B ≤ᵐ[volume.restrict (Icc a b)]
      (fun t => K * (E t / (ℓ / 2 + q t)^2)) from by
      filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Icc] with t ht hm
      exact ht (by simpa only [uIcc_of_le hab] using hm))
  rw [intervalIntegral.integral_const_mul] at H
  have HE := integral_energy_div_shift_sq_le hab hc hσ hq hn hE he
  have hlast : K * (2 / (ℓ / 2)) = 4 * K / ℓ := by ring
  exact H.trans (hlast ▸ mul_le_mul_of_nonneg_left HE hK)

/-- A total-mass bound extends a weak tail estimate above a fixed threshold to all
positive levels, without changing its inverse-level dependence. -/
theorem logarithmic_tail_bound_of_large_levels {T : ℝ → ℝ} {M C L : ℝ}
    (hM : 0 ≤ M) (htotal : ∀ ℓ, 0 < ℓ → T ℓ ≤ M)
    (hlarge : ∀ ℓ, 0 < ℓ → L ≤ ℓ → T ℓ ≤ C / ℓ) :
    ∀ ℓ, 0 < ℓ → T ℓ ≤ max C (L * M) / ℓ := by
  intro ℓ hℓ
  by_cases h : L ≤ ℓ
  · exact (hlarge ℓ hℓ h).trans (div_le_div_of_nonneg_right (le_max_left _ _) hℓ.le)
  · apply (le_div_iff₀ hℓ).mpr
    calc
      T ℓ * ℓ ≤ M * ℓ := mul_le_mul_of_nonneg_right (htotal ℓ hℓ) hℓ.le
      _ ≤ L * M := by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) hM]
      _ ≤ max C (L * M) := le_max_right _ _

end HeatKernel
