-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Hormander.B.Order
public import Hormander.B.Fractional.Taylor
public import Hormander.A.SobolevScale
public import Hormander.B.Fractional.Young

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Hormander.B

theorem norm_besselSymbol {N : ℕ} (s : ℝ) (ξ : Carrier N) :
    ‖Hormander.A.besselSymbol s ξ‖ = japBracket ξ ^ s := by
  have h := Real.rpow_nonneg (japBracket_pos ξ).le s
  simp only [Hormander.A.besselSymbol, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  rw [japBracket, bracketSq, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring


/-- The weighted Fourier integrand of a Schwartz function, as an extended nonnegative real. -/
def fourierWeightENN {N : ℕ} (s : ℝ) (u : TestFunction N) (ξ : Carrier N) : ℝ≥0∞ :=
  ENNReal.ofReal (japBracket ξ ^ s) * ‖𝓕 u ξ‖ₑ

theorem fourier_Lambda_apply {N : ℕ} (s : ℝ) (u : TestFunction N) (ξ : Carrier N) :
    𝓕 (Hormander.A.Lambda s u) ξ = Hormander.A.besselSymbol s ξ * 𝓕 u ξ := by
  rw [Hormander.A.fourier_Lambda,
    SchwartzMap.smulLeftCLM_apply_apply (Hormander.A.besselSymbol_hasTemperateGrowth s)]
  rfl

/-- The Sobolev norm of a Schwartz function is the weighted Fourier `L²` norm (squared form). -/
theorem sobolevNorm_sq_eq_lintegral {N : ℕ} (s : ℝ) (u : TestFunction N) :
    ENNReal.ofReal (sobolevNorm s u) ^ 2 = ∫⁻ ξ, fourierWeightENN s u ξ ^ 2 := by
  have h1 : sobolevNorm s u = ‖(𝓕 (Hormander.A.Lambda s u)).toLp 2‖ := by
    rw [sobolevNorm_eq_schwartzSobolevNorm, Hormander.A.schwartzSobolevNorm,
      ← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.norm_fourier_eq]
  rw [h1, SchwartzMap.norm_toLp, ENNReal.ofReal_toReal
    (MemLp.eLpNorm_ne_top ((𝓕 (Hormander.A.Lambda s u)).memLp 2 volume))]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (𝓕 (Hormander.A.Lambda s u)).continuous.aestronglyMeasurable]
  have hc : ∀ ξ, ‖𝓕 (Hormander.A.Lambda s u) ξ‖ₑ = fourierWeightENN s u ξ := by
    intro ξ
    rw [fourier_Lambda_apply, enorm_mul, fourierWeightENN, ← ofReal_norm,
      norm_besselSymbol]
  simp only [hc, ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp


theorem continuous_japBracket_rpow {N : ℕ} (s : ℝ) :
    Continuous fun ξ : Carrier N => japBracket ξ ^ s := by
  have hc : Continuous fun ξ : Carrier N => japBracket ξ := by
    unfold japBracket bracketSq
    fun_prop
  exact hc.rpow_const fun ξ => Or.inl (japBracket_pos ξ).ne'

theorem measurable_fourierWeightENN {N : ℕ} (s : ℝ) (u : TestFunction N) :
    Measurable (fourierWeightENN s u) := by
  unfold fourierWeightENN
  exact (ENNReal.measurable_ofReal.comp (continuous_japBracket_rpow s).measurable).mul
    (𝓕 u).continuous.enorm.measurable

theorem ofReal_sobolevNorm_le_of_sq {N : ℕ} {s₁ s₂ : ℝ} {u v : TestFunction N} {K : ℝ≥0∞}
    (hK : K ≠ ⊤)
    (h : ∫⁻ ξ, fourierWeightENN s₁ u ξ ^ 2 ≤ K ^ 2 * ∫⁻ ξ, fourierWeightENN s₂ v ξ ^ 2) :
    sobolevNorm s₁ u ≤ K.toReal * sobolevNorm s₂ v := by
  rw [← sobolevNorm_sq_eq_lintegral, ← sobolevNorm_sq_eq_lintegral] at h
  have h2 : ENNReal.ofReal (sobolevNorm s₁ u) ≤ K * ENNReal.ofReal (sobolevNorm s₂ v) := by
    rw [← mul_pow] at h
    exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 h
  have hnn : 0 ≤ K.toReal * sobolevNorm s₂ v :=
    mul_nonneg ENNReal.toReal_nonneg (by
      rw [sobolevNorm_eq_schwartzSobolevNorm, Hormander.A.schwartzSobolevNorm]; exact norm_nonneg _)
  rw [← ENNReal.ofReal_le_ofReal_iff hnn, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hK]
  exact h2

/-- A single convolution-type bound on weighted Fourier transforms gives an operator order. -/
theorem hasOrder_of_kernelBound {N : ℕ} (T : Operator N) (m : ℝ)
    (H : ∀ s : ℝ, ∃ k : Carrier N → ℝ≥0∞, Measurable k ∧ ∫⁻ a, k a ≠ ⊤ ∧
      ∀ (u : TestFunction N) (ξ : Carrier N),
        fourierWeightENN s (T u) ξ ≤ ∫⁻ a, k a * fourierWeightENN (s + m) u (ξ - a)) :
    HasOrder m T := by
  intro s
  obtain ⟨k, hk, hK, hb⟩ := H s
  refine ⟨(∫⁻ a, k a).toNNReal, fun u => ?_⟩
  have := young_dominated k _ _ hk (measurable_fourierWeightENN (s + m) u) hK (hb u)
  simpa [ENNReal.coe_toNNReal_eq_toReal] using ofReal_sobolevNorm_le_of_sq hK this

/-- A two-fold convolution-type bound on weighted Fourier transforms gives an operator order. -/
theorem hasOrder_of_kernelBound₂ {N : ℕ} (T : Operator N) (m : ℝ)
    (H : ∀ s : ℝ, ∃ k₁ k₂ : Carrier N → ℝ≥0∞, Measurable k₁ ∧ Measurable k₂ ∧
      ∫⁻ a, k₁ a ≠ ⊤ ∧ ∫⁻ a, k₂ a ≠ ⊤ ∧
      ∀ (u : TestFunction N) (ξ : Carrier N),
        fourierWeightENN s (T u) ξ ≤
          ∫⁻ a, k₁ a * ∫⁻ b, k₂ b * fourierWeightENN (s + m) u (ξ - a - b)) :
    HasOrder m T := by
  intro s
  obtain ⟨k₁, k₂, hk₁, hk₂, hK₁, hK₂, hb⟩ := H s
  refine ⟨((∫⁻ a, k₁ a) * (∫⁻ a, k₂ a)).toNNReal, fun u => ?_⟩
  have hf := measurable_fourierWeightENN (s + m) u
  have h2 := young_lintegral_sq k₂ _ hk₂ hf hK₂
  have h2m := measurable_kernelConv k₂ _ hk₂ hf
  have h1 := young_dominated k₁ _ _ hk₁ h2m hK₁ (hb u)
  have hKK : (∫⁻ a, k₁ a) * (∫⁻ a, k₂ a) ≠ ⊤ := ENNReal.mul_ne_top hK₁ hK₂
  have hmain : ∫⁻ ξ, fourierWeightENN s (T u) ξ ^ 2 ≤
      ((∫⁻ a, k₁ a) * (∫⁻ a, k₂ a)) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + m) u ξ ^ 2 := by
    calc _ ≤ _ := h1
      _ ≤ (∫⁻ a, k₁ a) ^ 2 * ((∫⁻ a, k₂ a) ^ 2 * ∫⁻ ξ, fourierWeightENN (s + m) u ξ ^ 2) := by
          gcongr
      _ = _ := by ring
  simpa [ENNReal.coe_toNNReal_eq_toReal] using ofReal_sobolevNorm_le_of_sq hKK hmain

end Hormander.B
