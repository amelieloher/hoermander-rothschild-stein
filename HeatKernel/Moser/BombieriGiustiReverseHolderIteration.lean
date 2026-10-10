-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiUniformIteration

/-! # Finite-exponent logarithmic reverse Hölder iteration

The larger moment supplies the outer logarithmic value. The smaller exponent is
chosen only in the range up to half the fixed exponent. Geometric estimates and
threshold summability are explicit inputs to the iteration theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The moment and logarithmic tail estimates give a three-quarter contraction
for a reverse Hölder inequality in the half-exponent range. -/
theorem bombieriGiusti_reverseHolder_large_value_contraction
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) {U : Set α} (hμU : μ U ≤ 1)
    {p₀ A C h x : ℝ} (hp₀ : 0 < p₀) (hC : 0 ≤ C)
    (hmoment : (∫⁻ y in U, f y ^ p₀ ∂μ) ≤ ENNReal.ofReal (Real.exp (p₀ * h)))
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (U ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hreverse : ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      x ≤ max 0 ((1 / p - 1 / p₀) * C +
        Real.log (∫⁻ y in U, f y ^ p ∂μ).toReal / p))
    (hlarge : bombieriGiustiUniformThreshold p₀ A (8 * (C + Real.log 2 + 1)) ≤ h) :
    x ≤ 3 / 4 * h := by
  let a := 8 * (C + Real.log 2 + 1)
  have ha : 0 < a := by
    dsimp [a]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have h₁ : 2 * a / p₀ ≤ h := (le_max_left _ _).trans hlarge
  have h₂ : 2 * A * Real.exp a ≤ h :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have h₃ : 1 ≤ h := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hh : 0 < h := lt_of_lt_of_le zero_lt_one h₃
  let p := a / h
  have hp : 0 < p := div_pos ha hh
  have hpp₀ : p ≤ p₀ / 2 := div_le_half_of_threshold hp₀ hh h₁
  have hph : p * h = a := div_mul_cancel₀ a hh.ne'
  have htail' : μ (U ∩ {y | ENNReal.ofReal (Real.exp (h / 2)) < f y}) ≤
      ENNReal.ofReal (Real.exp (-a)) := by
    apply (htail (h / 2) (half_pos hh)).trans
    apply ENNReal.ofReal_le_ofReal
    have he : A / (h / 2) = 2 * A / h := by ring
    rw [he]
    exact div_le_exp_neg_of_logarithmic_threshold hh h₂
  have hsmall := lintegral_small_moment_le_two_exp hf hμU hp hp₀ hpp₀ ha.le hph hmoment htail'
  have hlog := log_toReal_le_half_add_log_two ha.le hsmall
  have hbound : (1 / p - 1 / p₀) * C +
      Real.log (∫⁻ y in U, f y ^ p ∂μ).toReal / p ≤ 3 / 4 * h :=
    le_three_quarters_of_log_reverseHolder hp hp₀ hC hph le_rfl hlog le_rfl
  exact (hreverse p hp hpp₀).trans (max_le (by positivity) hbound)

/-- Summable thresholds give a bound on the earlier normalized logarithmic moment,
independent of the finite terminal moment bound. The reverse Hölder hypotheses
include every positive exponent up to half the fixed exponent. -/
theorem bombieriGiusti_log_bound_of_summable_reverseHolder_thresholds
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℕ → Set α)
    {p₀ A H : ℝ} (hp₀ : 0 < p₀) {h C : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hh : ∀ j, 0 ≤ h j)
    (hmono : ∀ j, h j ≤ h (j + 1)) (hbound : ∀ j, h j ≤ H)
    (hμU : ∀ j, μ (U j) ≤ 1)
    (hmoment : ∀ j, (∫⁻ y in U j, f y ^ p₀ ∂μ) ≤ ENNReal.ofReal (Real.exp (p₀ * h j)))
    (htail : ∀ j, ∀ ℓ : ℝ, 0 < ℓ →
      μ (U j ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hreverse : ∀ j, ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      h j ≤ max 0 ((1 / p - 1 / p₀) * C j +
        Real.log (∫⁻ y in U (j + 1), f y ^ p ∂μ).toReal / p))
    (hsum : Summable (fun j => (3 / 4 : ℝ) ^ j *
      bombieriGiustiUniformThreshold p₀ A (8 * (C j + Real.log 2 + 1)))) :
    h 0 ≤ ∑' j, (3 / 4 : ℝ) ^ j *
      bombieriGiustiUniformThreshold p₀ A (8 * (C j + Real.log 2 + 1)) := by
  apply le_tsum_of_threshold_contraction (by norm_num) (by norm_num) _ hh hmono _ hbound hsum
  · intro j
    exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
  · intro j hj
    exact bombieriGiusti_reverseHolder_large_value_contraction hf (hμU (j + 1)) hp₀ (hC j)
      (hmoment (j + 1)) (htail (j + 1)) (hreverse j) hj

end HeatKernel
