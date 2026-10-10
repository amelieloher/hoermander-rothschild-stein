-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Bounded nonlinear recursions for distribution functions

A supremum argument removes the terminal remainder in a sublinear recurrence.
Applied to the power-normalized distribution function on decreasing thresholds,
it gives a weak Sobolev bound with an explicit constant.
-/

@[expose] public section

namespace HeatKernel.Sobolev

/-- A bounded nonnegative sublinear recursion has a universal power bound. -/
theorem le_rpow_of_bounded_sublinear_recursion {f : ℕ → ℝ} {K b M : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hK : 0 ≤ K) (hb : 0 ≤ b) (hb₁ : b < 1)
    (hbound : ∀ n, f n ≤ M) (hstep : ∀ n, f n ≤ K * (f (n + 1)) ^ b) :
    f 0 ≤ K ^ (1 / (1 - b)) := by
  let S := sSup (Set.range f)
  have hbounded : BddAbove (Set.range f) := ⟨M, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  have hle (n : ℕ) : f n ≤ S := le_csSup hbounded (Set.mem_range_self n)
  have hS₀ : 0 ≤ S := (hf 0).trans (hle 0)
  have hS : S ≤ K * S ^ b := by
    apply csSup_le (Set.range_nonempty f)
    rintro _ ⟨n, rfl⟩
    exact (hstep n).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hf (n + 1)) (hle (n + 1)) hb) hK)
  by_cases hzero : S = 0
  · exact (hle 0).trans (hzero ▸ Real.rpow_nonneg hK _)
  have hSpos : 0 < S := lt_of_le_of_ne hS₀ (Ne.symm hzero)
  have hpower : S ^ (1 - b) ≤ K := by
    rw [Real.rpow_sub hSpos, Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hSpos b)).mpr hS
  have hroot := (Real.le_rpow_inv_iff_of_pos hS₀ hK (sub_pos.mpr hb₁)).mpr hpower
  exact (hle 0).trans (by simpa only [one_div] using hroot)

/-- A power-normalized dyadic tail recurrence implies a weak power bound. -/
theorem mul_rpow_le_of_tail_recursion {M : ℝ → ℝ} {K b p V t₀ : ℝ}
    (hM : ∀ t, 0 < t → 0 ≤ M t) (hV : 0 ≤ V)
    (hbound : ∀ t, 0 < t → M t ≤ V)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hb₁ : b < 1) (hp : 0 ≤ p) (ht₀ : 0 < t₀)
    (hstep : ∀ t, 0 < t →
      M t * t ^ p ≤ K * (M (t / 2) * (t / 2) ^ p) ^ b) :
    M t₀ * t₀ ^ p ≤ K ^ (1 / (1 - b)) := by
  let t : ℕ → ℝ := fun n => t₀ / (2 : ℝ) ^ n
  have ht (n : ℕ) : 0 < t n := div_pos ht₀ (by positivity)
  have ht_le (n : ℕ) : t n ≤ t₀ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr
    have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hsucc (n : ℕ) : t (n + 1) = t n / 2 := by
    dsimp [t]
    rw [pow_succ]
    ring
  have h := le_rpow_of_bounded_sublinear_recursion
    (f := fun n => M (t n) * (t n) ^ p)
    (fun n => mul_nonneg (hM _ (ht n)) (Real.rpow_nonneg (ht n).le _))
    hK hb hb₁ (M := V * t₀ ^ p)
    (fun n => mul_le_mul (hbound _ (ht n))
      (Real.rpow_le_rpow (ht n).le (ht_le n) hp)
      (Real.rpow_nonneg (ht n).le _) hV)
    (fun n => by simpa only [hsucc] using hstep (t n) (ht n))
  simpa only [t, pow_zero, div_one] using h

/-- Removing the normalizing power gives the usual distribution-function bound. -/
theorem tail_le_of_normalized_recursion {M : ℝ → ℝ} {K b p V t₀ : ℝ}
    (hM : ∀ t, 0 < t → 0 ≤ M t) (hV : 0 ≤ V)
    (hbound : ∀ t, 0 < t → M t ≤ V)
    (hK : 0 ≤ K) (hb : 0 ≤ b) (hb₁ : b < 1) (hp : 0 ≤ p) (ht₀ : 0 < t₀)
    (hstep : ∀ t, 0 < t →
      M t * t ^ p ≤ K * (M (t / 2) * (t / 2) ^ p) ^ b) :
    M t₀ ≤ K ^ (1 / (1 - b)) * t₀ ^ (-p) := by
  have h := mul_rpow_le_of_tail_recursion hM hV hbound hK hb hb₁ hp ht₀ hstep
  rw [Real.rpow_neg ht₀.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ht₀ p)).mpr h

end HeatKernel.Sobolev
