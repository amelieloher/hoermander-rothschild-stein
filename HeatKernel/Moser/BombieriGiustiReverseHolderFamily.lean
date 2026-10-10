-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiMomentBound
public import HeatKernel.Moser.BombieriGiustiUniformFamily

/-! # The finite-exponent Bombieri--Giusti bound for nested set families -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The normalized finite-exponent reverse Hölder form of the Bombieri--Giusti
lemma. Every pair of nested parameters and every exponent up to half the terminal
exponent has the same geometric constant. The larger moment is assumed finite,
and its numerical value does not enter the bound. -/
theorem lintegral_rpow_norm_le_bombieriGiustiConstant_of_reverseHolder_family
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℝ → Set α)
    {p₀ A C κ θ σ : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (hθσ : θ < σ) (hσ : σ < 1)
    (hUmono : MonotoneOn U (Icc θ 1)) (hμU : μ (U 1) ≤ 1)
    (hmoment : (∫⁻ y in U 1, f y ^ p₀ ∂μ) ≠ ⊤)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (U 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hreverse : ∀ σ' σ'' : ℝ, θ ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      (∫⁻ y in U σ', f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
        ENNReal.ofReal (C * (1 / (σ'' - σ')) ^ κ) ^ (1 / p - 1 / p₀) *
          (∫⁻ y in U σ'', f y ^ p ∂μ) ^ (1 / p)) :
    (∫⁻ y in U θ, f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
      ENNReal.ofReal (bombieriGiustiReverseHolderConstant p₀ A C κ (σ - θ)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have h1mem : (1 : ℝ) ∈ Icc θ 1 := ⟨hθσ.le.trans hσ.le, le_rfl⟩
  let V : ℕ → Set α := fun j => U (bombieriGiustiNestingParameter θ σ j)
  have hparameter (j : ℕ) : bombieriGiustiNestingParameter θ σ j ∈ Icc θ 1 :=
    ⟨(bombieriGiustiNestingParameter_bounds hθσ j).1,
      (bombieriGiustiNestingParameter_bounds hθσ j).2.le.trans hσ.le⟩
  have hgap (j : ℕ) : bombieriGiustiNestingParameter θ σ j <
      bombieriGiustiNestingParameter θ σ (j + 1) := by
    apply sub_pos.mp
    rw [bombieriGiustiNestingParameter_succ_sub]
    exact bombieriGiustiNestingGap_pos (sub_pos.mpr hθσ) j
  have hVmono (j : ℕ) : V j ⊆ V (j + 1) :=
    hUmono (hparameter j) (hparameter (j + 1)) (hgap j).le
  have hV1 (j : ℕ) : V j ⊆ U 1 := hUmono (hparameter j) h1mem (hparameter j).2
  have hreverseV (j : ℕ) (p : ℝ) (hp : 0 < p) (hpp₀ : p ≤ p₀ / 2) :
      (∫⁻ y in V j, f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
        ENNReal.ofReal (Real.exp ((1 / p - 1 / p₀) *
          bombieriGiustiNestingCost C κ (σ - θ) j)) *
            (∫⁻ y in V (j + 1), f y ^ p ∂μ) ^ (1 / p) := by
    have he := hreverse (bombieriGiustiNestingParameter θ σ j)
      (bombieriGiustiNestingParameter θ σ (j + 1)) (hparameter j).1
      (hgap j) (hparameter (j + 1)).2 p hp hpp₀
    rw [← exp_log_meanValueCost hCpos (sub_pos.mpr (hgap j)) κ,
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      bombieriGiustiNestingParameter_succ_sub,
      ← bombieriGiustiNestingCost_eq_log_gap C κ (sub_pos.mpr hθσ) j] at he
    simpa only [mul_comm] using he
  have he := lintegral_rpow_norm_le_bombieriGiustiConstant_of_reverseHolder_estimates hf
    V (U 1) hp₀ hA hC hκ (sub_pos.mpr hθσ) (by linarith)
    hVmono hV1 hμU hmoment htail hreverseV
  simpa only [V, bombieriGiustiNestingParameter_zero] using he

end HeatKernel
