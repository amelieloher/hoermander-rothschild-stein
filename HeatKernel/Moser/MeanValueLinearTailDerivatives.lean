-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueLinearTailPowers
import Mathlib.Tactic

/-! # Exact chain factors for positive powers with a linear upper tail -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel

/-- The power chain factor below the threshold, and its constant upper-tail continuation. -/
def linearTailPositivePowerSlope (M γ s : ℝ) : ℝ :=
  if 0 < s then if s < M then γ * s ^ (γ - 1) else M ^ (γ - 1) else 0

/-- On nonnegative values the test is exactly s times the truncated power of exponent γ−1. -/
theorem linearTailPositivePower_eq_mul_min_rpow {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (hs : 0 ≤ s) :
    linearTailPositivePower M γ s = s * (min s M) ^ (γ - 1) := by
  rcases eq_or_lt_of_le hs with hs | hs
  · subst s
    rw [linearTailPositivePower_zero hM.le (zero_lt_one.trans_le hγ), zero_mul]
  · rcases le_total s M with hsM | hMs
    · rw [linearTailPositivePower_eq_rpow hs.le hsM, min_eq_left hsM]
      have he := Real.rpow_add hs (γ - 1) 1
      rw [sub_add_cancel, Real.rpow_one] at he
      rw [he, mul_comm]
    · rw [linearTailPositivePower_eq_linear hM hMs, min_eq_right hMs, mul_comm]

/-- The chain factor is the classical derivative away from the two corner levels. -/
theorem linearTailPositivePowerSlope_eq_deriv {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (hs0 : s ≠ 0) (hsM : s ≠ M) :
    linearTailPositivePowerSlope M γ s = deriv (linearTailPositivePower M γ) s := by
  rcases lt_or_gt_of_ne hs0 with hs0 | h0s
  · have hd : HasDerivAt (linearTailPositivePower M γ) 0 s := by
      apply (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hs0] with t ht
      have hn : t - M ≤ 0 := sub_nonpos.mpr (ht.le.trans hM.le)
      simp only [linearTailPositivePower, boundedPositivePower, max_eq_left ht.le,
        min_eq_right hM.le, Real.zero_rpow (zero_lt_one.trans_le hγ).ne',
        max_eq_left hn, mul_zero, add_zero]
    simpa only [linearTailPositivePowerSlope, ite_eq_right (not_lt_of_ge hs0.le)] using
      hd.deriv.symm
  · rcases lt_or_gt_of_ne hsM with hsM | hMs
    · have hd : HasDerivAt (linearTailPositivePower M γ) (γ * s ^ (γ - 1)) s := by
        apply (Real.hasDerivAt_rpow_const (p := γ) (Or.inl h0s.ne')).congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds h0s hsM] with t ht
        exact linearTailPositivePower_eq_rpow ht.1.le ht.2.le
      simpa only [linearTailPositivePowerSlope, ite_eq_left h0s, ite_eq_left hsM] using
        hd.deriv.symm
    · have hd : HasDerivAt (linearTailPositivePower M γ) (M ^ (γ - 1)) s := by
        have hl : HasDerivAt (fun t : ℝ => M ^ (γ - 1) * t) (M ^ (γ - 1)) s := by
          simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul (M ^ (γ - 1))
        apply hl.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hMs] with t ht
        exact linearTailPositivePower_eq_linear hM ht.le
      simpa only [linearTailPositivePowerSlope, ite_eq_left h0s,
        ite_eq_right (not_lt_of_ge hMs.le)] using hd.deriv.symm

end HeatKernel
