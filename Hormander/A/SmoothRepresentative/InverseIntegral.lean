-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap VectorFourier
open scoped FourierTransform

namespace Hormander.A

/-- If the moments `‖ξ‖ⁿ ‖g ξ‖` are integrable for all `n ≤ q`, the
inverse Fourier integral `𝓕⁻ g` is of class `C^q`. Differentiation under the integral sign is
Mathlib's `Real.contDiff_fourier` composed with the reflection `x ↦ -x`. -/
theorem contDiff_fourierInv_of_integrable_moments {N : ℕ} {q : ℕ∞} {g : Carrier N → ℂ}
    (hg : ∀ n : ℕ, (n : ℕ∞) ≤ q → Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖g ξ‖)) :
    ContDiff ℝ q (𝓕⁻ g) := by
  have h : (𝓕⁻ g : Carrier N → ℂ) = fun x ↦ 𝓕 g (-x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg g x
  rw [h]
  exact (Real.contDiff_fourier hg).comp contDiff_neg

/-- The inverse Fourier integral of an integrable function is bounded
by the `L¹` norm. -/
theorem norm_fourierInv_le_integral_norm {N : ℕ} (g : Carrier N → ℂ) (x : Carrier N) :
    ‖𝓕⁻ g x‖ ≤ ∫ ξ, ‖g ξ‖ := by
  rw [Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext ξ
  simp

/-- Test-function pairing for the inverse Fourier integral of an
integrable function (Fubini). -/
theorem integral_smul_fourierInv_eq {N : ℕ} {g : Carrier N → ℂ} (hg : Integrable g)
    (φ : 𝓢(Carrier N, ℂ)) :
    ∫ x, φ x • 𝓕⁻ g x = ∫ ξ, 𝓕⁻ φ ξ • g ξ := by
  have hg' : Integrable (fun x ↦ g (-x)) := hg.comp_neg
  have hφ : Integrable (φ : Carrier N → ℂ) := φ.integrable
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Carrier N))
    Real.continuous_fourierChar continuous_inner hg' hφ
  have e1 : ∀ x, (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (Carrier N))
      (fun x ↦ g (-x)) x) = 𝓕⁻ g x := by
    intro x
    rw [Real.fourierInv_eq_fourier_comp_neg]
    rfl
  have e2 : ∀ x, VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ (Carrier N)).flip (φ : Carrier N → ℂ) x = 𝓕 (φ : Carrier N → ℂ) x := by
    intro x
    simp only [VectorFourier.fourierIntegral, Real.fourier_eq]
    congr 1
    funext v
    simp only [LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm]
  simp_rw [e1, e2] at key
  change _ = ∫ x, g (-x) • 𝓕 (φ : Carrier N → ℂ) x at key
  have e3 : ∀ ξ : Carrier N, (𝓕 (φ : Carrier N → ℂ)) (-ξ) = 𝓕⁻ φ ξ := fun ξ =>
    by rw [SchwartzMap.fourierInv_coe]; exact (Real.fourierInv_eq_fourier_neg _ _).symm
  calc ∫ x, φ x • 𝓕⁻ g x = ∫ ξ, 𝓕⁻ g ξ • φ ξ := by simp_rw [smul_eq_mul, mul_comm]
    _ = ∫ x, g (-x) • 𝓕 (φ : Carrier N → ℂ) x := key
    _ = ∫ x, g x • 𝓕 (φ : Carrier N → ℂ) (-x) := by
        rw [← integral_neg_eq_self (fun x => g x • 𝓕 (φ : Carrier N → ℂ) (-x)) volume]
        simp only [neg_neg]
    _ = ∫ ξ, 𝓕⁻ φ ξ • g ξ := by simp_rw [e3, smul_eq_mul, mul_comm]

/-- Derivative formula: under integrable moments up to order `q`, the
`n`-th Fréchet derivative of `𝓕⁻ g` is the inverse Fourier integral of
`ξ ↦ (2πi ⟨ξ, ·⟩)ⁿ g ξ` (Mathlib's `fourierPowSMulRight` with `L = -innerSL`). -/
theorem iteratedFDeriv_fourierInv_eq {N : ℕ} {q : ℕ∞} {g : Carrier N → ℂ}
    (hg : ∀ n : ℕ, (n : ℕ∞) ≤ q → Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖g ξ‖))
    (hgm : AEStronglyMeasurable g volume) {n : ℕ} (hn : (n : ℕ∞) ≤ q) :
    iteratedFDeriv ℝ n (𝓕⁻ g) =
      𝓕⁻ (fun ξ ↦ fourierPowSMulRight (-innerSL ℝ) g ξ n) := by
  have hg' : ∀ m : ℕ, (m : ℕ∞) ≤ q → Integrable (fun v : Carrier N ↦ ‖v‖ ^ m * ‖g (-v)‖) := by
    intro m hm
    simpa using (hg m hm).comp_neg
  rw [Real.fourierInv_eq_fourier_comp_neg, Real.fourierInv_eq_fourier_comp_neg,
    Real.iteratedFDeriv_fourier hg' (hgm.comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving) hn]
  congr 1
  funext v
  ext m
  simp [fourierPowSMulRight_apply]

/-- Derivative bound: `‖Dⁿ(𝓕⁻ g)(x)‖ ≤ (2π)ⁿ ∫ ‖ξ‖ⁿ ‖g ξ‖`. -/
theorem norm_iteratedFDeriv_fourierInv_le {N : ℕ} {q : ℕ∞} {g : Carrier N → ℂ}
    (hg : ∀ n : ℕ, (n : ℕ∞) ≤ q → Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖g ξ‖))
    (hgm : AEStronglyMeasurable g volume) {n : ℕ} (hn : (n : ℕ∞) ≤ q) (x : Carrier N) :
    ‖iteratedFDeriv ℝ n (𝓕⁻ g) x‖ ≤ (2 * Real.pi) ^ n * ∫ ξ, ‖ξ‖ ^ n * ‖g ξ‖ := by
  rw [iteratedFDeriv_fourierInv_eq hg hgm hn, Real.fourierInv_eq_fourier_neg, Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint := hg n hn
  calc ∫ v, ‖(𝐞 (-inner ℝ v (-x)) : ℂ) • fourierPowSMulRight (-innerSL ℝ) g v n‖
      ≤ ∫ v, (2 * Real.pi) ^ n * (‖v‖ ^ n * ‖g v‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hint.const_mul _) (Filter.Eventually.of_forall fun v => ?_)
        simp only [norm_smul, Circle.norm_coe, one_mul]
        have := norm_fourierPowSMulRight_le (-innerSL ℝ) g v n
        have h1 : ‖(-innerSL ℝ : Carrier N →L[ℝ] Carrier N →L[ℝ] ℝ)‖ ≤ 1 := by
          exact le_of_eq_of_le (norm_neg (innerSL ℝ : Carrier N →L[ℝ] Carrier N →L[ℝ] ℝ)) (norm_innerSL_le ℝ)
        calc _ ≤ _ := this
          _ ≤ _ := by
            have : (2 * Real.pi * ‖(-innerSL ℝ : Carrier N →L[ℝ] Carrier N →L[ℝ] ℝ)‖) ^ n ≤ (2 * Real.pi) ^ n := by
              refine pow_le_pow_left₀ (by positivity) ?_ n
              exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans_eq (mul_one _)
            nlinarith [mul_nonneg (pow_nonneg (norm_nonneg v) n) (norm_nonneg (g v))]
    _ = _ := by rw [integral_const_mul]

end Hormander.A
