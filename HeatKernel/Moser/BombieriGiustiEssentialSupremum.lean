-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiLogarithmicSupremum

/-! # Essential-supremum bounds from uniform moment and logarithmic-tail estimates

A finite outer essential supremum supplies the initial caps. Its numerical value
does not enter the resulting constant. The moment estimates and logarithmic tails
are explicit inputs, so local solution estimates can be substituted directly.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The uniform constant from the rational-nesting threshold series. -/
def bombieriGiustiUniformConstant (p₀ A C κ d : ℝ) : ℝ :=
  Real.exp (∑' j, (3 / 4 : ℝ) ^ j * bombieriGiustiUniformThreshold p₀ A
    (4 * (bombieriGiustiNestingCost C κ d j + Real.log 2 + 1)))

/-- The explicit uniform constant is strictly positive. -/
theorem bombieriGiustiUniformConstant_pos (p₀ A C κ d : ℝ) :
    0 < bombieriGiustiUniformConstant p₀ A C κ d := Real.exp_pos _

/-- Uniform small-moment mean-value estimates and a logarithmic tail bound give
an essential-supremum bound independent of the finite outer essential supremum.
The latter is an explicit local boundedness input. -/
theorem essSup_le_bombieriGiustiConstant_of_meanValue_and_finite_outer_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℕ → Set α) (V : Set α)
    {p₀ A C κ d : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hUmono : ∀ j, U j ⊆ U (j + 1)) (hUV : ∀ j, U j ⊆ V)
    (hμV : μ V ≤ 1) (hfinite : essSup f (μ.restrict V) ≠ ⊤)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (V ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hmean : ∀ j, ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      essSup f (μ.restrict (U j)) ≤
        (ENNReal.ofReal (Real.exp (bombieriGiustiNestingCost C κ d j)) *
          (∫⁻ y in U (j + 1), f y ^ p ∂μ)) ^ (1 / p)) :
    essSup f (μ.restrict (U 0)) ≤
      ENNReal.ofReal (bombieriGiustiUniformConstant p₀ A C κ d) := by
  let S : ℕ → ℝ≥0∞ := fun j => essSup f (μ.restrict (U j))
  let h : ℕ → ℝ := fun j => nonnegativeLogSupremum (S j)
  have hS (j : ℕ) : S j ≤ essSup f (μ.restrict V) :=
    essSup_mono_measure' (Measure.restrict_mono (hUV j) le_rfl)
  have hSfin (j : ℕ) : S j ≠ ⊤ := ne_top_of_le_ne_top hfinite (hS j)
  have hh (j : ℕ) : 0 ≤ h j := le_max_left _ _
  have hmono (j : ℕ) : h j ≤ h (j + 1) :=
    nonnegativeLogSupremum_mono (hSfin (j + 1))
      (essSup_mono_measure' (Measure.restrict_mono (hUmono j) le_rfl))
  have hbound (j : ℕ) : h j ≤ nonnegativeLogSupremum (essSup f (μ.restrict V)) :=
    nonnegativeLogSupremum_mono hfinite (hS j)
  have hμU (j : ℕ) : μ (U j) ≤ 1 := (measure_mono (hUV j)).trans hμV
  have hcap (j : ℕ) : ∀ᵐ y ∂μ.restrict (U j),
      f y ≤ ENNReal.ofReal (Real.exp (h j)) := by
    filter_upwards [ENNReal.ae_le_essSup f] with y hy
    exact hy.trans (le_exp_nonnegativeLogSupremum (hSfin j))
  have htail' (j : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
      μ (U j ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ) :=
    (measure_mono (inter_subset_inter_left _ (hUV j))).trans (htail ℓ hℓ)
  have hlogmean (j : ℕ) (p : ℝ) (hp : 0 < p) (hpp₀ : p ≤ p₀ / 2) :
      h j ≤ max 0 ((bombieriGiustiNestingCost C κ d j +
        Real.log (∫⁻ y in U (j + 1), f y ^ p ∂μ).toReal) / p) :=
    nonnegativeLogSupremum_le_of_meanValue hp
      (lintegral_rpow_ne_top_of_essSup_ne_top f (hUV (j + 1)) hμV hfinite hp.le)
      (hmean j p hp hpp₀)
  have hb := bombieriGiusti_log_bound_of_uniform_nesting_estimates hf U hp₀ hA hC hκ
    hd.le hd1 hh hmono hbound hμU hcap htail' hlogmean
  exact (le_exp_nonnegativeLogSupremum (hSfin 0)).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hb))

end HeatKernel
