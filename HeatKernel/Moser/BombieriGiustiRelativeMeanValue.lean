-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiMeasureNormalization

/-! # Uniform Bombieri--Giusti bounds with a finite reference measure -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The uniform mean-value form with moments divided by a positive finite outer
reference measure. Normalization preserves the essential supremum and removes
the outer measure from the final constant. -/
theorem essSup_le_bombieriGiustiConstant_of_relative_meanValue_estimates
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
    (hmean : ∀ σ' σ'' : ℝ, θ ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      essSup f (μ.restrict (U σ')) ≤
        (ENNReal.ofReal (C * (1 / (σ'' - σ')) ^ κ) * (μ (U 1))⁻¹ *
          (∫⁻ y in U σ'', f y ^ p ∂μ)) ^ (1 / p)) :
    essSup f (μ.restrict (U θ)) ≤
      ENNReal.ofReal (bombieriGiustiUniformConstant p₀ A C κ (σ - θ)) := by
  let ν := normalizedReferenceMeasure μ (U 1)
  have hνU : ν (U 1) ≤ 1 := (normalizedReferenceMeasure_reference hzero hfinite).le
  have hνmoment : (∫⁻ y in U 1, f y ^ p₀ ∂ν) ≠ ⊤ :=
    lintegral_normalizedReferenceMeasure_ne_top hzero (fun y => f y ^ p₀) (U 1) hmoment
  have hνtail (ℓ : ℝ) (hℓ : 0 < ℓ) :
      ν (U 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ) :=
    normalizedReferenceMeasure_le_of_relative_bound hzero hfinite (htail ℓ hℓ)
  have hνmean (σ' σ'' : ℝ) (hθ' : θ ≤ σ') (hlt : σ' < σ'') (hσ'' : σ'' ≤ 1)
      (p : ℝ) (hp : 0 < p) (hpp₀ : p ≤ p₀ / 2) :
      essSup f (ν.restrict (U σ')) ≤
        (ENNReal.ofReal (C * (1 / (σ'' - σ')) ^ κ) *
          (∫⁻ y in U σ'', f y ^ p ∂ν)) ^ (1 / p) := by
    rw [essSup_normalizedReferenceMeasure_restrict hfinite,
      lintegral_normalizedReferenceMeasure_restrict]
    simpa only [mul_assoc] using hmean σ' σ'' hθ' hlt hσ'' p hp hpp₀
  have he := essSup_le_bombieriGiustiConstant_of_uniform_moment_estimates
    hf U hp₀ hA hC hκ hθ hθσ hσ hUmono hνU hνmoment hνtail hνmean
  rwa [essSup_normalizedReferenceMeasure_restrict hfinite] at he

end HeatKernel
