-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.CommutatorFourier
public import Hormander.B.Fractional.KernelEstimates
public import Hormander.B.Fractional.SobolevFourier

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem continuous_peetreOmega_rpow (p : ℝ) : Continuous fun a : Carrier N => peetreOmega a ^ p := by
  have hc : Continuous fun a : Carrier N => peetreOmega a := by
    unfold peetreOmega japBracket bracketSq
    fun_prop
  exact hc.rpow_const fun a => Or.inl (peetreOmega_pos a).ne'

theorem lintegral_ofReal_ne_top_of_integrable {κ : Carrier N → ℝ} (h : Integrable κ) :
    ∫⁻ a, ENNReal.ofReal (κ a) ≠ ⊤ :=
  h.lintegral_lt_top.ne

/-- Single-integral transfer of a pointwise kernel bound to the weighted Fourier integrand. -/
theorem fw_le_single (s m : ℝ) (T : Operator N) (u : TestFunction N) (ξ : Carrier N)
    (G : Carrier N → ℂ) (hT : 𝓕 (T u) ξ = ∫ a, G a) (κ : Carrier N → ℝ)
    (hκ0 : ∀ a, 0 ≤ κ a)
    (hκ : ∀ a, japBracket ξ ^ s * ‖G a‖ ≤
      κ a * (japBracket (ξ - a) ^ (s + m) * ‖𝓕 u (ξ - a)‖)) :
    fourierWeightENN s (T u) ξ ≤
      ∫⁻ a, ENNReal.ofReal (κ a) * fourierWeightENN (s + m) u (ξ - a) := by
  have hJ : 0 ≤ japBracket ξ ^ s := Real.rpow_nonneg (japBracket_pos ξ).le s
  unfold fourierWeightENN
  rw [hT]
  calc ENNReal.ofReal (japBracket ξ ^ s) * ‖∫ a, G a‖ₑ
      ≤ ENNReal.ofReal (japBracket ξ ^ s) * ∫⁻ a, ‖G a‖ₑ :=
        mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
    _ = ∫⁻ a, ENNReal.ofReal (japBracket ξ ^ s) * ‖G a‖ₑ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ _ := by
        refine lintegral_mono fun a => ?_
        have hJ' : 0 ≤ japBracket (ξ - a) ^ (s + m) :=
          Real.rpow_nonneg (japBracket_pos _).le _
        rw [← ofReal_norm (G a), ← ENNReal.ofReal_mul hJ, ← ofReal_norm (𝓕 u (ξ - a)),
          ← ENNReal.ofReal_mul hJ', ← ENNReal.ofReal_mul (hκ0 a)]
        exact ENNReal.ofReal_le_ofReal (hκ a)

/-- Nested-integral transfer of a product kernel bound to the weighted Fourier integrand. -/
theorem fw_le_nested (s m : ℝ) (T : Operator N) (u : TestFunction N) (ξ : Carrier N)
    (G : Carrier N → Carrier N → ℂ) (hT : 𝓕 (T u) ξ = ∫ a, ∫ b, G a b)
    (κ₁ κ₂ : Carrier N → ℝ) (hκ₁ : ∀ a, 0 ≤ κ₁ a) (hκ₂ : ∀ b, 0 ≤ κ₂ b)
    (hκ : ∀ a b, japBracket ξ ^ s * ‖G a b‖ ≤
      κ₁ a * κ₂ b * (japBracket (ξ - a - b) ^ (s + m) * ‖𝓕 u (ξ - a - b)‖)) :
    fourierWeightENN s (T u) ξ ≤
      ∫⁻ a, ENNReal.ofReal (κ₁ a) * ∫⁻ b, ENNReal.ofReal (κ₂ b) *
        fourierWeightENN (s + m) u (ξ - a - b) := by
  have hJ : 0 ≤ japBracket ξ ^ s := Real.rpow_nonneg (japBracket_pos ξ).le s
  unfold fourierWeightENN
  rw [hT]
  calc ENNReal.ofReal (japBracket ξ ^ s) * ‖∫ a, ∫ b, G a b‖ₑ
      ≤ ENNReal.ofReal (japBracket ξ ^ s) * ∫⁻ a, ∫⁻ b, ‖G a b‖ₑ := by
        refine mul_le_mul_right ((enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono fun a => enorm_integral_le_lintegral_enorm _)) _
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (japBracket ξ ^ s) * ‖G a b‖ₑ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun a => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        refine lintegral_mono fun a => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun b => ?_
        have hJ' : 0 ≤ japBracket (ξ - a - b) ^ (s + m) :=
          Real.rpow_nonneg (japBracket_pos _).le _
        rw [← ofReal_norm (G a b), ← ENNReal.ofReal_mul hJ,
          ← ofReal_norm (𝓕 u (ξ - a - b)), ← ENNReal.ofReal_mul hJ',
          ← ENNReal.ofReal_mul (hκ₂ b), ← ENNReal.ofReal_mul (hκ₁ a)]
        refine ENNReal.ofReal_le_ofReal ((hκ a b).trans_eq ?_)
        ring

theorem norm_besselSym_sub (σ : ℝ) (x y : Carrier N) :
    ‖besselSym σ x - besselSym σ y‖ = |japBracket x ^ σ - japBracket y ^ σ| := by
  simp only [besselSym]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_symMixed (σ : ℝ) (ξ a b : Carrier N) :
    ‖symMixed σ ξ a b‖ = |japBracket ξ ^ σ - japBracket (ξ - a) ^ σ - japBracket (ξ - b) ^ σ +
      japBracket (ξ - a - b) ^ σ| := by
  simp only [symMixed, besselSym]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs]

theorem fourierNorm_nonneg (g : TestFunction N) (a : Carrier N) : 0 ≤ ‖𝓕 g a‖ := norm_nonneg _

/-- (first claim) `[Λ^σ, M_g]` has order `σ - 1`. -/
theorem fractionalCommutator_order (σ : ℝ) (g : TestFunction N) :
    HasOrder (σ - 1) (operatorComm (lambdaOperator σ) (multiplierOperator g)) := by
  apply hasOrder_of_kernelBound
  intro s
  set κ : Carrier N → ℝ := fun a => |σ| * (‖a‖ ^ 1 * (peetreOmega a ^ |s + σ - 1| * ‖𝓕 g a‖) +
    ‖a‖ ^ 1 * (peetreOmega a ^ |s| * ‖𝓕 g a‖)) with hκdef
  have hint : Integrable κ :=
    ((integrable_kernelWeight (𝓕 g) 1 |s + σ - 1|).add
      (integrable_kernelWeight (𝓕 g) 1 |s|)).const_mul |σ|
  have hκc : Continuous κ := by
    have hg : Continuous fun a : Carrier N => ‖𝓕 g a‖ := (𝓕 g).continuous.norm
    exact continuous_const.mul (((continuous_norm.pow 1).mul
      ((continuous_peetreOmega_rpow _).mul hg)).add ((continuous_norm.pow 1).mul
      ((continuous_peetreOmega_rpow _).mul hg)))
  have hκ0 : ∀ a, 0 ≤ κ a := fun a => by
    have := Real.rpow_nonneg (peetreOmega_pos a).le |s + σ - 1|
    have := Real.rpow_nonneg (peetreOmega_pos a).le |s|
    simp only [hκdef]; positivity
  refine ⟨fun a => ENNReal.ofReal (κ a),
    ENNReal.measurable_ofReal.comp hκc.measurable,
    lintegral_ofReal_ne_top_of_integrable hint, fun u ξ => ?_⟩
  refine fw_le_single s (σ - 1) _ u ξ _ (fourier_comm_mul σ g u ξ) κ hκ0 fun a => ?_
  rw [show s + (σ - 1) = s + σ - 1 by ring, norm_mul, norm_mul, norm_besselSym_sub]
  have hk := kernel_single_bound σ s ξ a
  have hg := fourierNorm_nonneg g a
  have hu := norm_nonneg (𝓕 u (ξ - a))
  calc japBracket ξ ^ s * (‖𝓕 g a‖ * (|japBracket ξ ^ σ - japBracket (ξ - a) ^ σ| *
        ‖𝓕 u (ξ - a)‖))
      = (japBracket ξ ^ s * |japBracket ξ ^ σ - japBracket (ξ - a) ^ σ|) *
          (‖𝓕 g a‖ * ‖𝓕 u (ξ - a)‖) := by ring
    _ ≤ (|σ| * ‖a‖ * (peetreOmega a ^ |s + σ - 1| + peetreOmega a ^ |s|) *
        japBracket (ξ - a) ^ (s + σ - 1)) * (‖𝓕 g a‖ * ‖𝓕 u (ξ - a)‖) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg hg hu)
    _ = _ := by simp only [hκdef]; ring

/-- (third claim) `[[Λ^σ, M_g], M_h]` has order `σ - 2`. -/
theorem fractionalCommutator_nested_order (σ : ℝ) (g h : TestFunction N) :
    HasOrder (σ - 2) (operatorComm (operatorComm (lambdaOperator σ) (multiplierOperator g))
      (multiplierOperator h)) := by
  apply hasOrder_of_kernelBound₂
  intro s
  set M := |s| + |σ - 2| with hM
  set K := 2 * gradConst σ * 2 ^ M with hK
  set κ₁ : Carrier N → ℝ := fun a => K * (‖a‖ ^ 1 * (peetreOmega a ^ M * ‖𝓕 g a‖)) with hκ₁def
  set κ₂ : Carrier N → ℝ := fun b => ‖b‖ ^ 1 * (peetreOmega b ^ M * ‖𝓕 h b‖) with hκ₂def
  have hint₁ : Integrable κ₁ := (integrable_kernelWeight (𝓕 g) 1 M).const_mul _
  have hint₂ : Integrable κ₂ := integrable_kernelWeight (𝓕 h) 1 M
  have hκ₁c : Continuous κ₁ :=
    continuous_const.mul ((continuous_norm.pow 1).mul
      ((continuous_peetreOmega_rpow _).mul (𝓕 g).continuous.norm))
  have hκ₂c : Continuous κ₂ :=
    (continuous_norm.pow 1).mul ((continuous_peetreOmega_rpow _).mul (𝓕 h).continuous.norm)
  have hK0 : 0 ≤ K := by
    have := gradConst_nonneg σ
    simp only [hK]; positivity
  have hκ₁0 : ∀ a, 0 ≤ κ₁ a := fun a => by
    have := Real.rpow_nonneg (peetreOmega_pos a).le M
    simp only [hκ₁def]; positivity
  have hκ₂0 : ∀ b, 0 ≤ κ₂ b := fun b => by
    have := Real.rpow_nonneg (peetreOmega_pos b).le M
    simp only [hκ₂def]; positivity
  refine ⟨fun a => ENNReal.ofReal (κ₁ a), fun b => ENNReal.ofReal (κ₂ b),
    ENNReal.measurable_ofReal.comp hκ₁c.measurable,
    ENNReal.measurable_ofReal.comp hκ₂c.measurable,
    lintegral_ofReal_ne_top_of_integrable hint₁, lintegral_ofReal_ne_top_of_integrable hint₂,
    fun u ξ => ?_⟩
  refine fw_le_nested s (σ - 2) _ u ξ _ (fourier_comm_nested σ g h u ξ) κ₁ κ₂ hκ₁0 hκ₂0
    fun a b => ?_
  simp only [tripleIntegrand]
  rw [show s + (σ - 2) = s + σ - 2 by ring, norm_mul, norm_mul, norm_mul, norm_symMixed]
  have hk := kernel_triple_bound σ s ξ a b
  have hg := fourierNorm_nonneg g a
  have hh := fourierNorm_nonneg h b
  have hu := norm_nonneg (𝓕 u (ξ - a - b))
  calc japBracket ξ ^ s * (‖𝓕 g a‖ * (‖𝓕 h b‖ * (|japBracket ξ ^ σ - japBracket (ξ - a) ^ σ -
        japBracket (ξ - b) ^ σ + japBracket (ξ - a - b) ^ σ| * ‖𝓕 u (ξ - a - b)‖)))
      = (japBracket ξ ^ s * |japBracket ξ ^ σ - japBracket (ξ - a) ^ σ -
        japBracket (ξ - b) ^ σ + japBracket (ξ - a - b) ^ σ|) *
        (‖𝓕 g a‖ * ‖𝓕 h b‖ * ‖𝓕 u (ξ - a - b)‖) := by ring
    _ ≤ (2 * gradConst σ * 2 ^ M * ((‖a‖ * peetreOmega a ^ M) * (‖b‖ * peetreOmega b ^ M)) *
        japBracket (ξ - a - b) ^ (s + σ - 2)) *
        (‖𝓕 g a‖ * ‖𝓕 h b‖ * ‖𝓕 u (ξ - a - b)‖) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg (mul_nonneg hg hh) hu)
    _ = _ := by simp only [hκ₁def, hκ₂def, hK]; ring

end Hormander.B
