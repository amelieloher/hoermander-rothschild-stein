-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiLogarithmicMoments

/-! # Finite-exponent bounds from reverse Hölder and logarithmic-tail estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The finite-exponent constant from the reverse Hölder threshold series. -/
def bombieriGiustiReverseHolderConstant (p₀ A C κ d : ℝ) : ℝ :=
  Real.exp (∑' j, (3 / 4 : ℝ) ^ j * bombieriGiustiUniformThreshold p₀ A
    (8 * (bombieriGiustiNestingCost C κ d j + Real.log 2 + 1)))

/-- The finite-exponent constant is strictly positive. -/
theorem bombieriGiustiReverseHolderConstant_pos (p₀ A C κ d : ℝ) :
    0 < bombieriGiustiReverseHolderConstant p₀ A C κ d := Real.exp_pos _

/-- Reverse Hölder inequalities along rational nesting and logarithmic tails
bound the initial moment norm independently of the finite outer moment's value.
The moment caps and the bounded logarithmic sequence are derived. -/
theorem lintegral_rpow_norm_le_bombieriGiustiConstant_of_reverseHolder_estimates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) (U : ℕ → Set α) (V : Set α)
    {p₀ A C κ d : ℝ} (hp₀ : 0 < p₀) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hκ : 0 ≤ κ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hUmono : ∀ j, U j ⊆ U (j + 1)) (hUV : ∀ j, U j ⊆ V)
    (hμV : μ V ≤ 1) (hmoment : (∫⁻ y in V, f y ^ p₀ ∂μ) ≠ ⊤)
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      μ (V ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ))
    (hreverse : ∀ j, ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      (∫⁻ y in U j, f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
        ENNReal.ofReal (Real.exp ((1 / p - 1 / p₀) * bombieriGiustiNestingCost C κ d j)) *
          (∫⁻ y in U (j + 1), f y ^ p ∂μ) ^ (1 / p)) :
    (∫⁻ y in U 0, f y ^ p₀ ∂μ) ^ (1 / p₀) ≤
      ENNReal.ofReal (bombieriGiustiReverseHolderConstant p₀ A C κ d) := by
  let m : ℕ → ℝ≥0∞ := fun j => ∫⁻ y in U j, f y ^ p₀ ∂μ
  let S : ℕ → ℝ≥0∞ := fun j => m j ^ (1 / p₀)
  let h : ℕ → ℝ := fun j => nonnegativeLogSupremum (S j)
  have hm (j : ℕ) : m j ≠ ⊤ := ne_top_of_le_ne_top hmoment (lintegral_mono_set (hUV j))
  have hSfin (j : ℕ) : S j ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp₀.le) (hm j)
  have hh (j : ℕ) : 0 ≤ h j := le_max_left _ _
  have hmono (j : ℕ) : h j ≤ h (j + 1) :=
    nonnegativeLogSupremum_mono (hSfin (j + 1))
      (ENNReal.rpow_le_rpow (lintegral_mono_set (hUmono j)) (one_div_nonneg.mpr hp₀.le))
  have hbound (j : ℕ) : h j ≤
      nonnegativeLogSupremum ((∫⁻ y in V, f y ^ p₀ ∂μ) ^ (1 / p₀)) :=
    nonnegativeLogSupremum_mono
      (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp₀.le) hmoment)
      (ENNReal.rpow_le_rpow (lintegral_mono_set (hUV j)) (one_div_nonneg.mpr hp₀.le))
  have hμU (j : ℕ) : μ (U j) ≤ 1 := (measure_mono (hUV j)).trans hμV
  have hcap (j : ℕ) : (∫⁻ y in U j, f y ^ p₀ ∂μ) ≤
      ENNReal.ofReal (Real.exp (p₀ * h j)) :=
    le_exp_mul_nonnegativeLogSupremum_rpow (hm j) hp₀
  have htail' (j : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
      μ (U j ∩ {y | ENNReal.ofReal (Real.exp ℓ) < f y}) ≤ ENNReal.ofReal (A / ℓ) :=
    (measure_mono (inter_subset_inter_left _ (hUV j))).trans (htail ℓ hℓ)
  have hlogreverse (j : ℕ) (p : ℝ) (hp : 0 < p) (hpp₀ : p ≤ p₀ / 2) :
      h j ≤ max 0 ((1 / p - 1 / p₀) * bombieriGiustiNestingCost C κ d j +
        Real.log (∫⁻ y in U (j + 1), f y ^ p ∂μ).toReal / p) :=
    nonnegativeLogSupremum_le_of_scaled_moment hp
      (lintegral_rpow_ne_top_of_le_exponent f (hμU (j + 1)) hp.le
        (by linarith) (hm (j + 1))) (hreverse j p hp hpp₀)
  have hb := bombieriGiusti_log_bound_of_reverseHolder_nesting_estimates hf U hp₀ hA hC hκ
    hd.le hd1 hh hmono hbound hμU hcap htail' hlogreverse
  exact (le_exp_nonnegativeLogSupremum (hSfin 0)).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hb))

end HeatKernel
