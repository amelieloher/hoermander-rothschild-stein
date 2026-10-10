-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiUniformIteration

/-! # Summability of logarithmic iteration thresholds

Logarithmic growth of the nesting cost gives a polynomial majorant for the
exponential thresholds. Multiplication by the geometric contraction factor then
gives summability, without a separate summability hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A shifted natural power has a polynomial majorant in the original index. -/
theorem pow_add_two_le_three_pow_mul (j k : ℕ) :
    ((j : ℝ) + 2) ^ k ≤ (3 : ℝ) ^ k * ((j : ℝ) ^ k + 1) := by
  by_cases hj : j = 0
  · subst j
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) k
    have hz : 0 ≤ (0 : ℝ) ^ k := pow_nonneg (by norm_num) k
    simp only [Nat.cast_zero, zero_add]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k]
  · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    calc
      _ ≤ (3 * (j : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = (3 : ℝ) ^ k * (j : ℝ) ^ k := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k]

/-- A logarithmic upper bound on the nesting cost yields a polynomial upper bound
on every threshold. The polynomial degree and constant depend only on the data. -/
theorem exists_polynomial_bound_bombieriGiusti_thresholds
    {p₀ A C D s : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 ≤ s)
    {cost : ℕ → ℝ} (hcost : ∀ j, cost j ≤ C + D * Real.log ((j : ℝ) + 2)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ k : ℕ, ∀ j,
      bombieriGiustiUniformThreshold p₀ A (s * (cost j + Real.log 2 + 1)) ≤
        B * ((j : ℝ) ^ k + 1) := by
  let α := s * (C + Real.log 2 + 1)
  obtain ⟨k, hk⟩ := exists_nat_ge (s * D)
  let B := (2 / p₀ + 2 * A + 1) * Real.exp α
  have hdiv : 0 ≤ 2 / p₀ := by positivity
  have hα : 0 ≤ α := by
    dsimp [α]
    exact mul_nonneg hs (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  have hexp : 1 ≤ Real.exp α := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hα
  have hB₀ : 0 ≤ B := by dsimp [B]; positivity
  have hB₁ : 1 ≤ B := by dsimp [B]; nlinarith
  have hBdiv : (2 / p₀) * Real.exp α ≤ B := by dsimp [B]; nlinarith [Real.exp_pos α]
  have hBA : (2 * A) * Real.exp α ≤ B := by dsimp [B]; nlinarith [Real.exp_pos α]
  refine ⟨B * (3 : ℝ) ^ k, mul_nonneg hB₀ (by positivity), k, fun j => ?_⟩
  let a := s * (cost j + Real.log 2 + 1)
  have hj : (1 : ℝ) ≤ (j : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hlog : 0 ≤ Real.log ((j : ℝ) + 2) := Real.log_nonneg hj
  have ha : a ≤ α + (k : ℝ) * Real.log ((j : ℝ) + 2) := by
    have h := mul_le_mul_of_nonneg_left (hcost j) hs
    have h' := mul_le_mul_of_nonneg_right hk hlog
    dsimp [a, α]
    nlinarith
  have hea : Real.exp a ≤ Real.exp α * ((j : ℝ) + 2) ^ k := by
    calc
      _ ≤ Real.exp (α + (k : ℝ) * Real.log ((j : ℝ) + 2)) := Real.exp_le_exp.mpr ha
      _ = _ := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hae : a ≤ Real.exp α * ((j : ℝ) + 2) ^ k :=
    (by linarith [Real.add_one_le_exp a] : a ≤ Real.exp a).trans hea
  have hpow : 1 ≤ ((j : ℝ) + 2) ^ k := one_le_pow₀ hj
  have hthreshold : bombieriGiustiUniformThreshold p₀ A a ≤ B * ((j : ℝ) + 2) ^ k := by
    apply max_le
    · calc
        2 * a / p₀ = (2 / p₀) * a := by ring
        _ ≤ (2 / p₀) * (Real.exp α * ((j : ℝ) + 2) ^ k) :=
          mul_le_mul_of_nonneg_left hae hdiv
        _ = ((2 / p₀) * Real.exp α) * ((j : ℝ) + 2) ^ k := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hBdiv (by positivity)
    · apply max_le
      · calc
          2 * A * Real.exp a ≤ (2 * A) * (Real.exp α * ((j : ℝ) + 2) ^ k) :=
            mul_le_mul_of_nonneg_left hea (by positivity)
          _ = ((2 * A) * Real.exp α) * ((j : ℝ) + 2) ^ k := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hBA (by positivity)
      · nlinarith
  exact hthreshold.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (pow_add_two_le_three_pow_mul j k) hB₀)

/-- Logarithmic nesting costs suffice for summability of the thresholds in either
the uniform mean-value or finite-exponent reverse Hölder iteration. -/
theorem summable_bombieriGiusti_thresholds_of_logarithmic_cost
    {p₀ A C D s : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 ≤ s)
    {cost : ℕ → ℝ} (hcost : ∀ j, cost j ≤ C + D * Real.log ((j : ℝ) + 2)) :
    Summable (fun j => (3 / 4 : ℝ) ^ j *
      bombieriGiustiUniformThreshold p₀ A (s * (cost j + Real.log 2 + 1))) := by
  obtain ⟨B, _, k, hk⟩ := exists_polynomial_bound_bombieriGiusti_thresholds hp₀ hA hC hs hcost
  exact summable_bombieriGiusti_thresholds_of_polynomial_bound
    (fun _ => (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)) k hk

end HeatKernel
