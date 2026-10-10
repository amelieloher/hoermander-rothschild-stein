-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Contractive iteration for reverse Hölder inequalities

Finite iteration and removal of a uniformly bounded terminal remainder. These scalar
lemmas apply to the logarithms of integral norms in the Bombieri–Giusti argument.
-/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace HeatKernel

/-- Iterate an affine contraction, keeping the terminal value and every error term. -/
theorem le_pow_mul_add_sum_of_contraction {h b : ℕ → ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hstep : ∀ j, h j ≤ q * h (j + 1) + b j) (n : ℕ) :
    h 0 ≤ q ^ n * h n + ∑ j ∈ range n, q ^ j * b j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := mul_le_mul_of_nonneg_left (hstep n) (pow_nonneg hq n)
    rw [sum_range_succ, pow_succ]
    nlinarith

/-- A bounded terminal remainder vanishes for a strict contraction. -/
theorem le_tsum_of_contraction_of_bounded {h b : ℕ → ℝ} {q H : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : ∀ j, 0 ≤ b j)
    (hstep : ∀ j, h j ≤ q * h (j + 1) + b j)
    (hbound : ∀ j, h j ≤ H) (hsum : Summable (fun j => q ^ j * b j)) :
    h 0 ≤ ∑' j, q ^ j * b j := by
  have hn (n : ℕ) : h 0 ≤ q ^ n * H + ∑' j, q ^ j * b j := by
    calc
      h 0 ≤ q ^ n * h n + ∑ j ∈ range n, q ^ j * b j :=
        le_pow_mul_add_sum_of_contraction hq hstep n
      _ ≤ q ^ n * H + ∑' j, q ^ j * b j := add_le_add
        (mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg hq n))
        (hsum.sum_le_tsum (range n) (fun j _ => mul_nonneg (pow_nonneg hq j) (hb j)))
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const H).add
    (tendsto_const_nhds (x := ∑' j, q ^ j * b j))
  simpa using ge_of_tendsto' ht hn

/-- Combining a large-value contraction with monotonicity gives an affine recurrence. -/
theorem le_mul_add_threshold {x y T q : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hy : 0 ≤ y) (hxy : x ≤ y) (hlarge : T ≤ y → x ≤ q * y) :
    x ≤ q * y + T := by
  by_cases h : T ≤ y
  · have := hlarge h
    linarith
  · have := mul_nonneg hq hy
    have := lt_of_not_ge h
    linarith

/-- The exponent chosen at a large logarithmic value stays in the half-range. -/
theorem div_le_half_of_threshold {a h p₀ : ℝ} (hp₀ : 0 < p₀) (hh : 0 < h)
    (hthreshold : 2 * a / p₀ ≤ h) : a / h ≤ p₀ / 2 := by
  apply (div_le_iff₀ hh).2
  have := (div_le_iff₀ hp₀).1 hthreshold
  nlinarith

/-- Polynomial errors are summable after multiplication by a strict geometric factor. -/
theorem summable_geometric_mul_polynomial {q C : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (k : ℕ) : Summable (fun j : ℕ => q ^ j * (C * (j : ℝ) ^ k)) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have hs := (summable_pow_mul_geometric_of_norm_lt_one k hnorm).mul_left C
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hs

/-- A logarithmic reverse Hölder inequality gives a three-quarter bound. -/
theorem le_three_quarters_of_log_reverseHolder
    {x h a p p₀ C L : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀)
    (hC : 0 ≤ C) (hph : p * h = a)
    (ha : 8 * (C + Real.log 2 + 1) ≤ a)
    (hL : L ≤ a / 2 + Real.log 2)
    (hx : x ≤ (1 / p - 1 / p₀) * C + L / p) : x ≤ 3 / 4 * h := by
  have hCp₀ : 0 ≤ C / p₀ := div_nonneg hC hp₀.le
  have hx' : x * p ≤ C + L := by
    have heq : ((1 / p - 1 / p₀) * C + L / p) * p =
        C + L - C / p₀ * p := by field_simp; ring
    have hm := mul_le_mul_of_nonneg_right hx hp.le
    rw [heq] at hm
    have := mul_nonneg hCp₀ hp.le
    linarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

/-- Large-value contraction and monotonicity yield a bound independent of terminal values. -/
theorem le_tsum_of_threshold_contraction {h T : ℕ → ℝ} {q H : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hT : ∀ j, 0 ≤ T j) (hh : ∀ j, 0 ≤ h j)
    (hmono : ∀ j, h j ≤ h (j + 1))
    (hlarge : ∀ j, T j ≤ h (j + 1) → h j ≤ q * h (j + 1))
    (hbound : ∀ j, h j ≤ H) (hsum : Summable (fun j => q ^ j * T j)) :
    h 0 ≤ ∑' j, q ^ j * T j := by
  apply le_tsum_of_contraction_of_bounded hq hq1 hT _ hbound hsum
  intro j
  exact le_mul_add_threshold hq (hT j) (hh (j + 1)) (hmono j) (hlarge j)

end HeatKernel
