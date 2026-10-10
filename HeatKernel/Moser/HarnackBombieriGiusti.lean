-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiRelativeMeanValue
public import HeatKernel.Moser.BombieriGiustiRelativeReverseHolder
public import HeatKernel.Moser.BombieriGiustiMeanValueNormalization
public import HeatKernel.Moser.HarnackShiftedBridge
import Mathlib.Tactic

/-! # Harnack comparison from the two Bombieri--Giusti estimates

The earlier reverse Hölder estimate bounds a fixed moment, which the supplied
mean-value estimate turns into an upper bound. The later reciprocal estimate
bounds the reciprocal directly. The same logarithmic shift cancels between the
two sides, and a sequence of positive perturbations removes the lower shift.
All moment, tail, and mean-value estimates are explicit hypotheses.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The earlier fixed-exponent mean-value estimate and reverse Hölder family,
the later reciprocal mean-value family, and their two logarithmic tails imply
the essential-extremum comparison. All estimates use the same shift for each
positive perturbation, with constants independent of both shifts. -/
theorem essSup_ofReal_le_mul_essInf_ofReal_of_perturbed_bombieriGiusti_estimates
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : α → ℝ} (hu : Measurable u) (Sminus Splus P : Set α)
    (Uminus Uplus : ℝ → Set α)
    {p₀ Aminus Aplus Cminus Cplus κminus κplus θminus θplus σminus σplus K R : ℝ}
    (hp₀ : 0 < p₀) (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (hCminus : 1 ≤ Cminus) (hCplus : 1 ≤ Cplus)
    (hκminus : 0 ≤ κminus) (hκplus : 0 ≤ κplus)
    (hθminus : 0 ≤ θminus) (hθσminus : θminus < σminus) (hσminus : σminus < 1)
    (hθplus : 0 ≤ θplus) (hθσplus : θplus < σplus) (hσplus : σplus < 1)
    (hK : 0 < K) (hR : 0 < R)
    (hUminus : MonotoneOn Uminus (Icc θminus 1))
    (hUplus : MonotoneOn Uplus (Icc θplus 1))
    (hminuszero : μ (Uminus 1) ≠ 0) (hminusfinite : μ (Uminus 1) ≠ ⊤)
    (hpluszero : μ (Uplus 1) ≠ 0) (hplusfinite : μ (Uplus 1) ≠ ⊤)
    (hPzero : μ P ≠ 0) (hPminus : P ⊆ Uminus θminus)
    (hratio : μ (Uminus 1) ≤ ENNReal.ofReal R * μ P)
    (hSplus : Splus ⊆ Uplus θplus)
    (hunonneg : ∀ᵐ y ∂μ.restrict Splus, 0 ≤ u y)
    (hestimates : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
      let fminus : α → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
      let fplus : α → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp c / (u y + ε))
      (∫⁻ y in Uminus 1, fminus y ^ p₀ ∂μ) ≠ ⊤ ∧
      (∫⁻ y in Uplus 1, fplus y ^ p₀ ∂μ) ≠ ⊤ ∧
      (∀ ℓ : ℝ, 0 < ℓ →
        μ (Uminus 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < fminus y}) ≤
          ENNReal.ofReal (Aminus / ℓ) * μ (Uminus 1)) ∧
      (∀ ℓ : ℝ, 0 < ℓ →
        μ (Uplus 1 ∩ {y | ENNReal.ofReal (Real.exp ℓ) < fplus y}) ≤
          ENNReal.ofReal (Aplus / ℓ) * μ (Uplus 1)) ∧
      (∀ σ' σ'' : ℝ, θminus ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
        ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
        (∫⁻ y in Uminus σ', fminus y ^ p₀ ∂μ) ^ (1 / p₀) ≤
          (ENNReal.ofReal (Cminus * (1 / (σ'' - σ')) ^ κminus) *
            (μ (Uminus 1))⁻¹) ^ (1 / p - 1 / p₀) *
              (∫⁻ y in Uminus σ'', fminus y ^ p ∂μ) ^ (1 / p)) ∧
      (∀ σ' σ'' : ℝ, θplus ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
        ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
        essSup fplus (μ.restrict (Uplus σ')) ≤
          (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
            (μ (Uplus 1))⁻¹ * (∫⁻ y in Uplus σ'', fplus y ^ p ∂μ)) ^ (1 / p)) ∧
      essSup fminus (μ.restrict Sminus) ≤ ENNReal.ofReal K *
        ((μ P)⁻¹ * (∫⁻ y in P, fminus y ^ p₀ ∂μ)) ^ (1 / p₀)) :
    essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict Sminus) ≤
      ENNReal.ofReal
        (K * R ^ (1 / p₀) *
          bombieriGiustiReverseHolderConstant p₀ Aminus Cminus κminus (σminus - θminus) *
          bombieriGiustiUniformConstant p₀ Aplus Cplus κplus (σplus - θplus)) *
        essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict Splus) := by
  let Bminus := bombieriGiustiReverseHolderConstant
    p₀ Aminus Cminus κminus (σminus - θminus)
  let Bplus := bombieriGiustiUniformConstant p₀ Aplus Cplus κplus (σplus - θplus)
  have hBminus : 0 < Bminus := bombieriGiustiReverseHolderConstant_pos _ _ _ _ _
  have hBplus : 0 < Bplus := bombieriGiustiUniformConstant_pos _ _ _ _ _
  have hKR : 0 < K * R ^ (1 / p₀) := mul_pos hK (Real.rpow_pos_of_pos hR _)
  have hθminus1 : θminus ≤ 1 := hθσminus.le.trans hσminus.le
  have hPouter : P ⊆ Uminus 1 := hPminus.trans
    (hUminus ⟨le_rfl, hθminus1⟩ ⟨hθminus1, le_rfl⟩ hθminus1)
  apply essSup_ofReal_le_mul_essInf_ofReal_of_shifted_reciprocal_bounds
    (mul_pos hKR hBminus) hBplus hunonneg
  intro ε hε
  obtain ⟨c, hmomentminus, hmomentplus, htailminus, htailplus, hreverse, hmean, hfixed⟩ :=
    hestimates ε hε
  let fminus : α → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
  let fplus : α → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp c / (u y + ε))
  have hfminus : Measurable fminus :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hu.add_const ε))
  have hfplus : Measurable fplus :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (hu.add_const ε))
  have hm := lintegral_rpow_norm_le_bombieriGiustiConstant_of_relative_reverseHolder_estimates
    hfminus Uminus hp₀ hAminus hCminus hκminus hθminus hθσminus hσminus
    hUminus hminuszero hminusfinite hmomentminus htailminus hreverse
  have hp := essSup_le_bombieriGiustiConstant_of_relative_meanValue_estimates
    hfplus Uplus hp₀ hAplus hCplus hκplus hθplus hθσplus hσplus
    hUplus hpluszero hplusfinite hmomentplus htailplus hmean
  have hfixed' := essSup_le_normalized_moment_of_measure_comparison
    hp₀ hK.le hR.le hPzero hminusfinite hPminus hPouter hratio hfixed
  have hm' : essSup fminus (μ.restrict Sminus) ≤
      ENNReal.ofReal (K * R ^ (1 / p₀) * Bminus) := by
    rw [ENNReal.ofReal_mul hKR.le]
    exact hfixed'.trans (mul_le_mul' le_rfl hm)
  have hp' : essSup fplus (μ.restrict Splus) ≤ ENNReal.ofReal Bplus :=
    (essSup_mono_measure' (Measure.restrict_mono hSplus le_rfl)).trans hp
  refine ⟨c, ?_, ?_⟩
  · filter_upwards [ENNReal.ae_le_essSup fminus] with y hy
    exact (ENNReal.ofReal_le_ofReal_iff (mul_pos hKR hBminus).le).mp (hy.trans hm')
  · filter_upwards [ENNReal.ae_le_essSup fplus] with y hy
    exact (ENNReal.ofReal_le_ofReal_iff hBplus.le).mp (hy.trans hp')

end HeatKernel
