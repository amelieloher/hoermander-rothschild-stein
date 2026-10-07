-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.FourierConvolution
public import Hormander.A.SobolevScale
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Hormander.A

/-- The rescaled kernel has the same unit mass as the original kernel. -/
theorem Jδ_norm_integral_one {N : ℕ} (δ : ℝ) (hδ : 0 < δ) :
    ∫ x : Carrier N, ‖Jδ N δ hδ x‖ = 1 := by
  have hpoint (x : Carrier N) :
    ‖Jδ N δ hδ x‖ = (δ ^ N)⁻¹ * J N (δ⁻¹ • x) := by
    rw [Jδ_apply, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt (pow_pos hδ N)))]
    rw [Jc_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (J_nonneg (δ⁻¹ • x))]
  calc
    ∫ x : Carrier N, ‖Jδ N δ hδ x‖ =
        ∫ x : Carrier N, (δ ^ N)⁻¹ * J N (δ⁻¹ • x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (δ ^ N)⁻¹ * (δ ^ Module.finrank ℝ (Carrier N) * ∫ x : Carrier N, J N x) := by
      rw [integral_const_mul]
      congr 2
      exact MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume (J N) hδ.le
    _ = 1 := by
      rw [finrank_euclideanSpace, Fintype.card_fin, J_integral_one]
      have hpow : (δ ^ N : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hδ)
      field_simp

/-- The Fourier transform of a Schwartz function is bounded by its L1 norm. -/
theorem fourier_schwartz_norm_le_integral {N : ℕ} (f : 𝓢(Carrier N, ℂ)) (ξ : Carrier N) :
    ‖SchwartzMap.fourierTransformCLM ℂ f ξ‖ ≤ ∫ x : Carrier N, ‖f x‖ := by
  calc
    ‖SchwartzMap.fourierTransformCLM ℂ f ξ‖ =
        ‖∫ x : Carrier N, 𝐞 (-inner ℝ x ξ) • f x‖ := by
      rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, Real.fourier_eq]
    _ ≤ ∫ x : Carrier N, ‖𝐞 (-inner ℝ x ξ) • f x‖ := norm_integral_le_integral_norm _
    _ = ∫ x : Carrier N, ‖f x‖ := by simp

/-- The Fourier transform of the rescaled nonnegative unit-mass kernel is bounded by one. -/
theorem fourier_Jδ_norm_le_one {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (ξ : Carrier N) :
    ‖SchwartzMap.fourierTransformCLM ℂ (Jδ N δ hδ) ξ‖ ≤ 1 := by
  calc
    ‖SchwartzMap.fourierTransformCLM ℂ (Jδ N δ hδ) ξ‖ ≤
        ∫ x : Carrier N, ‖Jδ N δ hδ x‖ :=
      fourier_schwartz_norm_le_integral (Jδ N δ hδ) ξ
    _ = 1 := Jδ_norm_integral_one δ hδ

/-- Mollification agrees with the tempered-distribution Fourier multiplier. -/
theorem Sδ_eq_fourierMultiplier {N : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (T : 𝓢'(Carrier N, ℂ)) :
    Sδ N δ hδ T = TemperedDistribution.fourierMultiplierCLM ℂ
      (fun ξ => 𝓕 (Jδ N δ hδ) ξ) T := by
  calc
    Sδ N δ hδ T = 𝓕⁻ (𝓕 (Sδ N δ hδ T)) := by simp
    _ = 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => 𝓕 (Jδ N δ hδ) ξ) (𝓕 T)) := by rw [fourier_Sδ]
    _ = _ := by rw [TemperedDistribution.fourierMultiplierCLM_apply]

end Hormander.A
