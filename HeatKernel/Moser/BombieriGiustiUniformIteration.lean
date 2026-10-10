-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderMoments

/-! # Uniform mean-value iteration from logarithmic tails

The logarithmic mean-value inequality, essential caps on the outer sets, and a
common logarithmic tail bound imply a contractive recurrence. The summability
input is stated explicitly; a polynomial bound on the thresholds suffices.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace HeatKernel

/-- The threshold ensuring both the small-exponent range and exponential tail decay. -/
def bombieriGiustiUniformThreshold (p₀ A a : ℝ) : ℝ :=
  max (2 * a / p₀) (max (2 * A * Real.exp a) 1)

/-- The logarithmic mean-value inequality gives a contraction once the small moment has its
two-piece bound. -/
theorem le_three_quarters_of_log_meanValue {x h a p C L : ℝ}
    (hp : 0 < p) (hph : p * h = a) (ha : 4 * (C + Real.log 2 + 1) ≤ a)
    (hL : L ≤ a / 2 + Real.log 2) (hx : x ≤ (C + L) / p) : x ≤ 3 / 4 * h := by
  have hx' := (le_div_iff₀ hp).mp hx
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

/-- At a large outer logarithmic value, a uniform mean-value estimate and the
logarithmic tail bound give a three-quarter contraction. All quantities are
normalized by the outer reference measure. -/
theorem bombieriGiusti_uniform_large_value_contraction {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) {U : Set α} (hμU : μ U ≤ 1)
    {p₀ A C h x : ℝ} (hp₀ : 0 < p₀) (hC : 0 ≤ C)
    (hcap : ∀ᵐ y ∂μ.restrict U, f y ≤ ENNReal.ofReal (Real.exp h))
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (U ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hmean : ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      x ≤ max 0 ((C + Real.log (∫⁻ y in U, f y ^ p ∂μ).toReal) / p))
    (hlarge : bombieriGiustiUniformThreshold p₀ A (4 * (C + Real.log 2 + 1)) ≤ h) :
    x ≤ 3 / 4 * h := by
  let a := 4 * (C + Real.log 2 + 1)
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
  have hmoment : (∫⁻ y in U, f y ^ p₀ ∂μ) ≤ ENNReal.ofReal (Real.exp (p₀ * h)) := by
    calc
      _ ≤ ∫⁻ _y in U, ENNReal.ofReal (Real.exp h) ^ p₀ ∂μ :=
        lintegral_mono_ae (hcap.mono fun _ hy => ENNReal.rpow_le_rpow hy hp₀.le)
      _ = ENNReal.ofReal (Real.exp (p₀ * h)) * μ U := by
        rw [lintegral_const, Measure.restrict_apply_univ,
          ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm h p₀]
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_right hμU (ENNReal.ofReal (Real.exp (p₀ * h)))
  have htail' : μ (U ∩ {y | ENNReal.ofReal (Real.exp (h / 2)) < f y}) ≤
      ENNReal.ofReal (Real.exp (-a)) := by
    have he : A / (h / 2) = 2 * A / h := by ring
    apply (htail (h / 2) (half_pos hh)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [he]
    exact div_le_exp_neg_of_logarithmic_threshold hh h₂
  have hsmall := lintegral_small_moment_le_two_exp hf hμU hp hp₀ hpp₀ ha.le hph hmoment htail'
  have hlog := log_toReal_le_half_add_log_two ha.le hsmall
  have hbound : (C + Real.log (∫⁻ y in U, f y ^ p ∂μ).toReal) / p ≤ 3 / 4 * h :=
    le_three_quarters_of_log_meanValue hp hph le_rfl hlog le_rfl
  exact (hmean p hp hpp₀).trans (max_le (by positivity) hbound)

/-- Summable thresholds remove the terminal logarithmic supremum from uniform
mean-value iteration. The logarithmic mean-value and cap hypotheses are explicit
so geometric applications can supply their actual solution estimates. -/
theorem bombieriGiusti_log_bound_of_summable_uniform_thresholds
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℕ → Set α)
    {p₀ A H : ℝ} (hp₀ : 0 < p₀) {h C : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hh : ∀ j, 0 ≤ h j)
    (hmono : ∀ j, h j ≤ h (j + 1)) (hbound : ∀ j, h j ≤ H)
    (hμU : ∀ j, μ (U j) ≤ 1)
    (hcap : ∀ j, ∀ᵐ y ∂μ.restrict (U j), f y ≤ ENNReal.ofReal (Real.exp (h j)))
    (htail : ∀ j, ∀ ℓ : ℝ, 0 < ℓ →
      μ (U j ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hmean : ∀ j, ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      h j ≤ max 0 ((C j + Real.log (∫⁻ y in U (j + 1), f y ^ p ∂μ).toReal) / p))
    (hsum : Summable (fun j => (3 / 4 : ℝ) ^ j *
      bombieriGiustiUniformThreshold p₀ A (4 * (C j + Real.log 2 + 1)))) :
    h 0 ≤ ∑' j, (3 / 4 : ℝ) ^ j *
      bombieriGiustiUniformThreshold p₀ A (4 * (C j + Real.log 2 + 1)) := by
  apply le_tsum_of_threshold_contraction (by norm_num) (by norm_num) _ hh hmono _ hbound hsum
  · intro j
    exact (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
  · intro j hj
    exact bombieriGiusti_uniform_large_value_contraction hf (hμU (j + 1)) hp₀ (hC j)
      (hcap (j + 1)) (htail (j + 1)) (hmean j) hj

/-- A polynomial majorant suffices for summability of the geometric thresholds. -/
theorem summable_bombieriGiusti_thresholds_of_polynomial_bound {T : ℕ → ℝ}
    (hT : ∀ j, 0 ≤ T j) {D : ℝ} (k : ℕ)
    (hpoly : ∀ j, T j ≤ D * ((j : ℝ) ^ k + 1)) :
    Summable (fun j => (3 / 4 : ℝ) ^ j * T j) := by
  have hs := (summable_geometric_mul_polynomial (C := D) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) k).add
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_right D)
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (hT j)) _ hs
  intro j
  calc
    (3 / 4 : ℝ) ^ j * T j ≤ (3 / 4 : ℝ) ^ j * (D * ((j : ℝ) ^ k + 1)) :=
      mul_le_mul_of_nonneg_left (hpoly j) (by positivity)
    _ = _ := by ring

end HeatKernel
