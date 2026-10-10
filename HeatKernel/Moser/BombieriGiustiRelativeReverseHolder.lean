-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiNormNormalization

/-! # Reverse Hölder Bombieri--Giusti bounds with a finite reference measure -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The finite-exponent reverse Hölder form with its original reference-measure
factor and exponent difference. Normalizing the moments removes that factor from
the geometric cost and yields a uniform averaged terminal-moment bound. -/
theorem lintegral_rpow_norm_le_bombieriGiustiConstant_of_relative_reverseHolder_estimates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℝ → Set α)
    {p₀ A C κ θ σ : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (hθσ : θ < σ) (hσ : σ < 1)
    (hUmono : MonotoneOn U (Icc θ 1))
    (hzero : μ (U 1) ≠ 0) (hfinite : μ (U 1) ≠ ⊤)
    (hmoment : (∫⁻ y in U 1, f y ^ p₀ ∂μ) ≠ ⊤)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (U 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤
        ENNReal.ofReal (A / ℓ) * μ (U 1))
    (hreverse : ∀ σ' σ'' : ℝ, θ ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      (∫⁻ y in U σ', f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
        (ENNReal.ofReal (C * (1 / (σ'' - σ')) ^ κ) * (μ (U 1))⁻¹) ^
          (1 / p - 1 / p₀) * (∫⁻ y in U σ'', f y ^ p ∂μ) ^ (1 / p)) :
    ((μ (U 1))⁻¹ * (∫⁻ y in U θ, f y ^ p₀ ∂μ)) ^ (1 / p₀) ≤
      ENNReal.ofReal (bombieriGiustiReverseHolderConstant p₀ A C κ (σ - θ)) := by
  let ν := normalizedReferenceMeasure μ (U 1)
  have hνU : ν (U 1) ≤ 1 := (normalizedReferenceMeasure_reference hzero hfinite).le
  have hνmoment : (∫⁻ y in U 1, f y ^ p₀ ∂ν) ≠ ⊤ :=
    lintegral_normalizedReferenceMeasure_ne_top hzero (fun y => f y ^ p₀) (U 1) hmoment
  have hνtail (ℓ : ℝ) (hℓ : 0 < ℓ) :
      ν (U 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ) :=
    normalizedReferenceMeasure_le_of_relative_bound hzero hfinite (htail ℓ hℓ)
  have hνreverse (σ' σ'' : ℝ) (hθ' : θ ≤ σ') (hlt : σ' < σ'') (hσ'' : σ'' ≤ 1)
      (p : ℝ) (hp : 0 < p) (hpp₀ : p ≤ p₀ / 2) :
      (∫⁻ y in U σ', f y ^ p₀ ∂ν) ^ (1 / p₀) ≤
        ENNReal.ofReal (C * (1 / (σ'' - σ')) ^ κ) ^ (1 / p - 1 / p₀) *
          (∫⁻ y in U σ'', f y ^ p ∂ν) ^ (1 / p) := by
    rw [lintegral_normalizedReferenceMeasure_restrict,
      lintegral_normalizedReferenceMeasure_restrict]
    exact reverseHolder_norm_bound_mul_normalization (by simp [hfinite]) (by simp [hzero])
      hp hp₀ (by linarith) (hreverse σ' σ'' hθ' hlt hσ'' p hp hpp₀)
  have he := lintegral_rpow_norm_le_bombieriGiustiConstant_of_reverseHolder_family
    hf U hp₀ hA hC hκ hθ hθσ hσ hUmono hνU hνmoment hνtail hνreverse
  rwa [lintegral_normalizedReferenceMeasure_restrict] at he

end HeatKernel
