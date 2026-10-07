-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter Finset
open scoped Topology
namespace RothschildStein.H3

/-- A uniform geometric-sum bound with its explicit denominator. -/
theorem finite_geometric_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ range n, r ^ i ≤ 1 / (1 - r) := by
  have he : (1 - r) * ∑ i ∈ range n, r ^ i = 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, mul_add, ih, pow_succ]; ring
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  nlinarith [pow_nonneg hr n]

/-- Iterating an inhomogeneous scalar recurrence, with no
regularity assumption on the sequence (BB Lemma 8.55, p. 385). -/
theorem holeFilling_finite_iteration {f : ℕ → ℝ} {θ s A B : ℝ}
    (hθ : 0 ≤ θ)
    (hstep : ∀ n, f n ≤ θ * f (n + 1) + A * s ^ n + B) (n : ℕ) :
    f 0 ≤ θ ^ n * f n + A * (∑ i ∈ range n, (θ * s) ^ i) +
      B * (∑ i ∈ range n, θ ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := mul_le_mul_of_nonneg_left (hstep n) (pow_nonneg hθ n)
    calc
      f 0 ≤ θ ^ n * f n + A * (∑ i ∈ range n, (θ * s) ^ i) +
        B * (∑ i ∈ range n, θ ^ i) := ih
      _ ≤ θ ^ n * (θ * f (n + 1) + A * s ^ n + B) +
        A * (∑ i ∈ range n, (θ * s) ^ i) +
        B * (∑ i ∈ range n, θ ^ i) := by linarith
      _ = _ := by rw [sum_range_succ, sum_range_succ, pow_succ, mul_pow]; ring

/-- Boundedness kills the tail, including contraction zero.
The constants 2 and 3/2 are uniform for theta < 1/3. -/
theorem holeFilling_recursive_bound {f : ℕ → ℝ} {θ s A B M : ℝ}
    (hθ : 0 ≤ θ) (hθ3 : θ < 1 / 3) (hs : 0 ≤ s) (hθs : θ * s ≤ 1 / 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : ∀ n, f n ≤ M)
    (hstep : ∀ n, f n ≤ θ * f (n + 1) + A * s ^ n + B) :
    f 0 ≤ 2 * A + (3 / 2) * B := by
  have hθ1 : θ < 1 := by linarith
  have hrs : 0 ≤ θ * s := mul_nonneg hθ hs
  have hrs1 : θ * s < 1 := by linarith
  have hsum1 (n : ℕ) : (∑ i ∈ range n, θ ^ i) ≤ 3 / 2 := by
    apply (finite_geometric_sum_le hθ hθ1 n).trans
    apply (div_le_iff₀ (sub_pos.mpr hθ1)).mpr
    linarith
  have hsum2 (n : ℕ) : (∑ i ∈ range n, (θ * s) ^ i) ≤ 2 := by
    apply (finite_geometric_sum_le hrs hrs1 n).trans
    apply (div_le_iff₀ (sub_pos.mpr hrs1)).mpr
    linarith
  have hn (n : ℕ) : f 0 ≤ θ ^ n * M + (2 * A + (3 / 2) * B) := by
    have hh := holeFilling_finite_iteration hθ hstep n
    have ht := mul_le_mul_of_nonneg_left (hb n) (pow_nonneg hθ n)
    have ha := mul_le_mul_of_nonneg_left (hsum2 n) hA
    have hb' := mul_le_mul_of_nonneg_left (hsum1 n) hB
    linarith
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const M
  have hlim : Tendsto (fun n : ℕ => θ ^ n * M + (2 * A + (3 / 2) * B)) atTop
      (𝓝 (2 * A + (3 / 2) * B)) := by
    simpa only [zero_mul, zero_add] using ht.add_const (2 * A + (3 / 2) * B)
  exact ge_of_tendsto' hlim hn

end RothschildStein.H3
