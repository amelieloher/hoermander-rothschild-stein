-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.Contraction

@[expose] public section

noncomputable section

open ContinuousLinearMap MeasureTheory SchwartzMap
open scoped FourierTransform

namespace Hormander.A

/-- Dilation of the kernel dilates its Fourier transform:
`𝓕 (Jδ) ξ = 𝓕 (Jc) (δ ξ)` (change of variables `x = δ y` in the Fourier integral). -/
theorem fourier_Jδ_apply {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (ξ : Carrier N) :
    𝓕 (Jδ N δ hδ) ξ = 𝓕 (Jc N) (δ • ξ) := by
  change (∫ x, 𝐞 (-inner ℝ x ξ) • Jδ N δ hδ x) = ∫ y, 𝐞 (-inner ℝ y (δ • ξ)) • Jc N y
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have h1 : (∫ x : Carrier N, 𝐞 (-inner ℝ x ξ) • Jδ N δ hδ x) =
      (δ ^ N : ℝ)⁻¹ • ∫ x : Carrier N, 𝐞 (-inner ℝ x ξ) • Jc N (δ⁻¹ • x) := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Jδ_apply]
    rw [Complex.real_smul]
    exact (mul_smul_comm _ _ _).symm
  rw [h1]
  have h2 := Measure.integral_comp_smul (μ := (volume : Measure (Carrier N)))
    (fun y : Carrier N => 𝐞 (-inner ℝ (δ • y) ξ) • Jc N y) δ⁻¹
  have h3 : (fun x : Carrier N => 𝐞 (-inner ℝ (δ • δ⁻¹ • x) ξ) • Jc N (δ⁻¹ • x)) =
      fun x : Carrier N => 𝐞 (-inner ℝ x ξ) • Jc N (δ⁻¹ • x) := by
    funext x
    rw [smul_smul, mul_inv_cancel₀ hδ0, one_smul]
  have h4 : (fun y : Carrier N => 𝐞 (-inner ℝ (δ • y) ξ) • Jc N y) =
      fun y : Carrier N => 𝐞 (-inner ℝ y (δ • ξ)) • Jc N y := by
    funext y
    rw [real_inner_smul_left, real_inner_smul_right]
  simp only [h3, h4] at h2
  rw [h2, abs_of_pos (by positivity), inv_pow, inv_inv, finrank_euclideanSpace,
    Fintype.card_fin, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hδ0), one_smul]

/-- The Fourier transform of the complexified kernel is one at the
origin, because the kernel has total integral one. -/
theorem fourier_Jc_zero {N : ℕ} : 𝓕 (Jc N) 0 = 1 := by
  change (∫ x : Carrier N, 𝐞 (-inner ℝ x (0 : Carrier N)) • Jc N x) = 1
  have h : ∀ x : Carrier N, 𝐞 (-inner ℝ x (0 : Carrier N)) • Jc N x = ((J N x : ℝ) : ℂ) := by
    intro x
    simp
  simp only [h]
  rw [integral_complex_ofReal, J_integral_one]
  simp

/-- The dilated Fourier multiplier has temperate growth. -/
theorem hasTemperateGrowth_fourier_dilate {N : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    (fun ξ : Carrier N => 𝓕 (Jc N) (δ • ξ)).HasTemperateGrowth := by
  have h : (fun ξ : Carrier N => 𝓕 (Jc N) (δ • ξ)) = fun ξ => 𝓕 (Jδ N δ hδ) ξ := by
    funext ξ
    exact (fourier_Jδ_apply δ hδ ξ).symm
  rw [h]
  exact (𝓕 (Jδ N δ hδ)).hasTemperateGrowth

/-- Mollification of a Schwartz test is the inverse Fourier transform of
the dilated multiplier `𝓕 Jc (δ ·)` times the inverse Fourier transform of the test. -/
theorem SδSchwartz_eq_fourier_smulLeft {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (ψ : 𝓢(Carrier N, ℂ)) :
    SδSchwartz N δ hδ ψ =
      𝓕 (SchwartzMap.smulLeftCLM ℂ (fun ξ : Carrier N => 𝓕 (Jc N) (δ • ξ)) (𝓕⁻ ψ)) := by
  have h := fourier_SδSchwartz δ hδ (𝓕⁻ ψ)
  rw [FourierTransform.fourier_fourierInv_eq] at h
  rw [h]
  have hf : (fun ξ : Carrier N => 𝓕 (Jc N) (δ • ξ)) = fun ξ => 𝓕 (Jδ N δ hδ) ξ := by
    funext ξ
    exact (fourier_Jδ_apply δ hδ ξ).symm
  rw [hf]

end Hormander.A
