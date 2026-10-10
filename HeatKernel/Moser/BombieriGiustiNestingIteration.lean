-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiNesting
public import HeatKernel.Moser.BombieriGiustiReverseHolderIteration

/-! # Uniform bounds for rationally nested logarithmic iterations

The normalized moment or essential-cap inputs and the adjacent logarithmic
estimates are explicit. The nesting costs, threshold summability, and removal
of the finite terminal bound are discharged by the iteration argument.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Uniform mean-value estimates along the quadratic-gap nesting give a bound
depending only on the tail, exponent, and geometric constants. -/
theorem bombieriGiusti_log_bound_of_uniform_nesting_estimates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℕ → Set α)
    {p₀ A C κ d H : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hd1 : d ≤ 1) {h : ℕ → ℝ}
    (hh : ∀ j, 0 ≤ h j) (hmono : ∀ j, h j ≤ h (j + 1)) (hbound : ∀ j, h j ≤ H)
    (hμU : ∀ j, μ (U j) ≤ 1)
    (hcap : ∀ j, ∀ᵐ y ∂μ.restrict (U j), f y ≤ ENNReal.ofReal (Real.exp (h j)))
    (htail : ∀ j, ∀ ℓ : ℝ, 0 < ℓ →
      μ (U j ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hmean : ∀ j, ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      h j ≤ max 0 ((bombieriGiustiNestingCost C κ d j +
        Real.log (∫⁻ y in U (j + 1), f y ^ p ∂μ).toReal) / p)) :
    h 0 ≤ ∑' j, (3 / 4 : ℝ) ^ j * bombieriGiustiUniformThreshold p₀ A
      (4 * (bombieriGiustiNestingCost C κ d j + Real.log 2 + 1)) := by
  exact bombieriGiusti_log_bound_of_summable_uniform_thresholds hf U hp₀
    (bombieriGiustiNestingCost_nonneg hC hκ hd hd1) hh hmono hbound hμU hcap htail hmean
    (summable_bombieriGiusti_thresholds_nesting hp₀ hA hC hκ hd hd1 (by norm_num))

/-- Finite-exponent reverse Hölder estimates along the quadratic-gap nesting give
a bound independent of the supplied finite terminal moment bound. -/
theorem bombieriGiusti_log_bound_of_reverseHolder_nesting_estimates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℕ → Set α)
    {p₀ A C κ d H : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hd1 : d ≤ 1) {h : ℕ → ℝ}
    (hh : ∀ j, 0 ≤ h j) (hmono : ∀ j, h j ≤ h (j + 1)) (hbound : ∀ j, h j ≤ H)
    (hμU : ∀ j, μ (U j) ≤ 1)
    (hmoment : ∀ j, (∫⁻ y in U j, f y ^ p₀ ∂μ) ≤ ENNReal.ofReal (Real.exp (p₀ * h j)))
    (htail : ∀ j, ∀ ℓ : ℝ, 0 < ℓ →
      μ (U j ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hreverse : ∀ j, ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      h j ≤ max 0 ((1 / p - 1 / p₀) * bombieriGiustiNestingCost C κ d j +
        Real.log (∫⁻ y in U (j + 1), f y ^ p ∂μ).toReal / p)) :
    h 0 ≤ ∑' j, (3 / 4 : ℝ) ^ j * bombieriGiustiUniformThreshold p₀ A
      (8 * (bombieriGiustiNestingCost C κ d j + Real.log 2 + 1)) := by
  exact bombieriGiusti_log_bound_of_summable_reverseHolder_thresholds hf U hp₀
    (bombieriGiustiNestingCost_nonneg hC hκ hd hd1) hh hmono hbound hμU hmoment htail hreverse
    (summable_bombieriGiusti_thresholds_nesting hp₀ hA hC hκ hd hd1 (by norm_num))

end HeatKernel
