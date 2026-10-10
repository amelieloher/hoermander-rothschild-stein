-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiFiniteMoments

/-! # The uniform Bombieri--Giusti bound for nested measurable-set families

The finite larger moment and the outer mean-value estimate supply the finite
terminal supremum. Rational nesting and logarithmic-tail iteration then remove
its value from the final constant.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The logarithmic geometric cost exponentiates to the mean-value gap factor. -/
theorem exp_log_meanValueCost {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (κ : ℝ) :
    Real.exp (Real.log C + κ * Real.log (1 / δ)) = C * (1 / δ) ^ κ := by
  rw [Real.exp_add, Real.exp_log hC, Real.rpow_def_of_pos (one_div_pos.mpr hδ)]
  congr 2
  ring

/-- The normalized uniform mean-value form of the Bombieri--Giusti lemma.
Every smaller exponent has the same geometric constant. Finite larger moment
membership supplies the outer bound, which is absent from the resulting constant. -/
theorem essSup_le_bombieriGiustiConstant_of_uniform_moment_estimates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℝ → Set α)
    {p₀ A C κ θ σ : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (hθσ : θ < σ) (hσ : σ < 1)
    (hUmono : MonotoneOn U (Icc θ 1)) (hμU : μ (U 1) ≤ 1)
    (hmoment : (∫⁻ y in U 1, f y ^ p₀ ∂μ) ≠ ⊤)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (U 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hmean : ∀ σ' σ'' : ℝ, θ ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      essSup f (μ.restrict (U σ')) ≤
        (ENNReal.ofReal (C * (1 / (σ'' - σ')) ^ κ) *
          (∫⁻ y in U σ'', f y ^ p ∂μ)) ^ (1 / p)) :
    essSup f (μ.restrict (U θ)) ≤
      ENNReal.ofReal (bombieriGiustiUniformConstant p₀ A C κ (σ - θ)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hhalf : 0 < p₀ / 2 := half_pos hp₀
  have hmhalf := lintegral_rpow_ne_top_of_le_exponent f hμU hhalf.le
    (by linarith : p₀ / 2 ≤ p₀) hmoment
  have hσmem : σ ∈ Icc θ 1 := ⟨hθσ.le, hσ.le⟩
  have h1mem : (1 : ℝ) ∈ Icc θ 1 := ⟨hθσ.le.trans hσ.le, le_rfl⟩
  have hV1 : U σ ⊆ U 1 := hUmono hσmem h1mem hσ.le
  have hfinite : essSup f (μ.restrict (U σ)) ≠ ⊤ := by
    have he := hmean σ 1 hθσ.le hσ le_rfl (p₀ / 2) hhalf le_rfl
    exact ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hhalf.le)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmhalf)) he
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
  have hVσ (j : ℕ) : V j ⊆ U σ :=
    hUmono (hparameter j) hσmem (bombieriGiustiNestingParameter_bounds hθσ j).2.le
  have htailσ (ℓ : ℝ) (hℓ : 0 < ℓ) :
      μ (U σ ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ) :=
    (measure_mono (inter_subset_inter_left _ hV1)).trans (htail ℓ hℓ)
  have hmeanV (j : ℕ) (p : ℝ) (hp : 0 < p) (hpp₀ : p ≤ p₀ / 2) :
      essSup f (μ.restrict (V j)) ≤
        (ENNReal.ofReal (Real.exp (bombieriGiustiNestingCost C κ (σ - θ) j)) *
          (∫⁻ y in V (j + 1), f y ^ p ∂μ)) ^ (1 / p) := by
    have he := hmean (bombieriGiustiNestingParameter θ σ j)
      (bombieriGiustiNestingParameter θ σ (j + 1)) (hparameter j).1
      (hgap j) (hparameter (j + 1)).2 p hp hpp₀
    rw [← exp_log_meanValueCost hCpos (sub_pos.mpr (hgap j)) κ,
      bombieriGiustiNestingParameter_succ_sub,
      ← bombieriGiustiNestingCost_eq_log_gap C κ (sub_pos.mpr hθσ) j] at he
    exact he
  have he := essSup_le_bombieriGiustiConstant_of_meanValue_and_finite_outer_bound hf
    V (U σ) hp₀ hA hC hκ (sub_pos.mpr hθσ) (by linarith)
    hVmono hVσ ((measure_mono hV1).trans hμU) hfinite htailσ hmeanV
  simpa only [V, bombieriGiustiNestingParameter_zero] using he

end HeatKernel
