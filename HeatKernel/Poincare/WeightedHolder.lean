-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.MeanInequalities

/-! # Weighted Hölder inequality for finite chains

The weights in this estimate may vanish. The endpoint exponent one is included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators NNReal

namespace HeatKernel

/-- Weighted Hölder inequality, in power form, for a finite family of nonnegative numbers. -/
theorem rpow_sum_mul_le_sum_mul_sum_rpow {ι : Type*} (s : Finset ι)
    (w h : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, w i * h i) ^ p ≤
      (∑ i ∈ s, w i) ^ (p - 1) * ∑ i ∈ s, w i * h i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hwp : ∀ i, (w i ^ (1 / p)) ^ p = w i := fun i =>
    NNReal.rpow_self_rpow_inv hpq.ne_zero (w i)
  have hwq : ∀ i, (w i ^ (1 / q)) ^ q = w i := fun i =>
    NNReal.rpow_self_rpow_inv hpq.symm.ne_zero (w i)
  have hsum : ∀ i, w i ^ (1 / q) * (w i ^ (1 / p) * h i) = w i * h i := by
    intro i
    rw [← mul_assoc, ← NNReal.rpow_add_of_nonneg _ hpq.symm.one_div_pos.le
      hpq.one_div_pos.le, one_div, one_div, hpq.symm.inv_add_inv_eq_one, NNReal.rpow_one]
  have hconj : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  have h := NNReal.rpow_le_rpow
    (NNReal.inner_le_Lp_mul_Lq s (fun i => w i ^ (1 / q))
      (fun i => w i ^ (1 / p) * h i) hpq.symm) hpq.nonneg
  simpa only [hsum, NNReal.mul_rpow, hwp, hwq, ← NNReal.rpow_mul,
    hconj, one_div_mul_cancel hpq.ne_zero, NNReal.rpow_one] using h

/-- A bound on the sum of the weights gives the corresponding weighted power estimate. -/
theorem rpow_sum_mul_le_of_sum_le {ι : Type*} (s : Finset ι)
    (w h : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) {R : ℝ≥0}
    (hw : ∑ i ∈ s, w i ≤ R) :
    (∑ i ∈ s, w i * h i) ^ p ≤
      R ^ (p - 1) * ∑ i ∈ s, w i * h i ^ p := by
  exact (rpow_sum_mul_le_sum_mul_sum_rpow s w h hp).trans
    (mul_le_mul (NNReal.rpow_le_rpow hw (sub_nonneg.mpr hp)) le_rfl
      (by positivity) (by positivity))

end HeatKernel
