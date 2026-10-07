-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.Kernel
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

noncomputable section

open ContinuousLinearMap MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform Convolution

namespace Hormander.A

/-- The Fourier transform of an even Schwartz function is even. -/
theorem fourier_even_of_even {N : ℕ} (f : 𝓢(Carrier N, ℂ))
    (hf : ∀ x, f (-x) = f x) (ξ : Carrier N) :
    𝓕 f (-ξ) = 𝓕 f ξ := by
  change (∫ x, 𝐞 (-inner ℝ x (-ξ)) • f x) =
    ∫ x, 𝐞 (-inner ℝ x ξ) • f x
  calc
    (∫ x, 𝐞 (-inner ℝ x (-ξ)) • f x) =
        ∫ x, 𝐞 (-inner ℝ x ξ) • f (-x) := by
          rw [← integral_neg_eq_self]
          apply integral_congr_ae
          filter_upwards with x
          simp only [inner_neg_left, inner_neg_right, neg_neg]
    _ = ∫ x, 𝐞 (-inner ℝ x ξ) • f x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hf]

/-- Fourier convolution identifies the Fourier transform of the Schwartz mollifier. -/
theorem fourier_SδSchwartz {N : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (ψ : 𝓢(Carrier N, ℂ)) :
    SδSchwartz N δ hδ (𝓕 ψ) =
      𝓕 (SchwartzMap.smulLeftCLM ℂ (fun ξ => 𝓕 (Jδ N δ hδ) ξ) ψ) := by
  let K := Jδ N δ hδ
  let g : 𝓢(Carrier N, ℂ) := 𝓕 K
  have hg : ∀ ξ, g (-ξ) = g ξ := by
    intro ξ
    exact fourier_even_of_even K (Jδ_even δ hδ) ξ
  have hdouble (φ : 𝓢(Carrier N, ℂ)) (x : Carrier N) :
      𝓕 (𝓕 φ) x = φ (-x) := by
    have h1 : 𝓕⁻ (𝓕 φ) = φ := FourierTransform.fourierInv_fourier_eq φ
    have h2 := Real.fourierInv_eq_fourier_neg (fun y => 𝓕 φ y) (-x)
    rw [neg_neg] at h2
    have h3 : (𝓕⁻ (𝓕 φ)) (-x) = 𝓕⁻ (fun y => 𝓕 φ y) (-x) := by
      rw [SchwartzMap.fourierInv_coe]
    rw [h1] at h3
    rw [h3, h2, SchwartzMap.fourier_coe]
  apply (fourier_schwartz_bijective (N := N)).1
  ext ξ
  rw [SδSchwartz_eq_convolution]
  change 𝓕 (SchwartzMap.convolution (lsmul ℂ ℂ) (𝓕 ψ) (Jδ N δ hδ)) ξ =
    𝓕 (𝓕 (SchwartzMap.smulLeftCLM ℂ g ψ)) ξ
  rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
  rw [hdouble (SchwartzMap.smulLeftCLM ℂ g ψ)]
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
  rw [hdouble ψ]
  simp [g, K, hg, smul_eq_mul, mul_comm]

/-- Fourier transform turns distributional mollification
into multiplication by the Fourier transform of its kernel. -/
theorem fourier_Sδ {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (T : 𝓢'(Carrier N, ℂ)) :
    𝓕 (Sδ N δ hδ T) =
      TemperedDistribution.smulLeftCLM ℂ (fun ξ => 𝓕 (Jδ N δ hδ) ξ) (𝓕 T) := by
  ext ψ
  rw [tempered_fourier_apply, Sδ_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    tempered_fourier_apply]
  change T (SδSchwartz N δ hδ (𝓕 ψ)) =
    T (𝓕 (SchwartzMap.smulLeftCLM ℂ (fun ξ => 𝓕 (Jδ N δ hδ) ξ) ψ))
  congr 1
  exact fourier_SδSchwartz δ hδ ψ

end Hormander.A
