-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Fourier
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

noncomputable section

open ContinuousLinearMap MeasureTheory SchwartzMap TemperedDistribution
open scoped Convolution FourierTransform

namespace Hormander.A

/-- A symmetric bump whose support lies in the closed half-radius ball. -/
def jBump (N : ℕ) : ContDiffBump (0 : Carrier N) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The real compactly supported kernel used for mollification. -/
def J (N : ℕ) : 𝓢(Carrier N, ℝ) := by
  exact ((jBump N).hasCompactSupport_normed (μ := volume)).toSchwartzMap
    (jBump N).contDiff_normed

/-- The complexification of the real mollifier. -/
def Jc (N : ℕ) : 𝓢(Carrier N, ℂ) := by
  let f : Carrier N → ℂ := fun x ↦ (J N x : ℂ)
  have hsupp : HasCompactSupport f := by
    rw [hasCompactSupport_def]
    have hs : Function.support f = Function.support ((jBump N).normed volume) := by
      ext x
      simp [f, J, jBump]
    rw [hs]
    exact (jBump N).hasCompactSupport_normed (μ := volume)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact Complex.ofRealCLM.contDiff.comp (jBump N).contDiff_normed
  exact hsupp.toSchwartzMap hsm

/-- Evaluation of the complexified kernel is the complex cast of the real kernel. -/
@[simp] theorem Jc_apply (N : ℕ) (x : Carrier N) : Jc N x = (J N x : ℂ) := rfl

/-- The rescaled Schwartz mollifier `δ⁻ᴺ J(x / δ)`. -/
def Jδ (N : ℕ) (δ : ℝ) (hδ : 0 < δ) : 𝓢(Carrier N, ℂ) :=
  (δ ^ N : ℝ)⁻¹ •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 δ⁻¹ (inv_ne_zero (ne_of_gt hδ))))
      (Jc N)

/-- Pointwise formula for the rescaled mollifier. -/
@[simp] theorem Jδ_apply (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (x : Carrier N) :
    Jδ N δ hδ x = (((δ ^ N : ℝ)⁻¹ : ℝ) : ℂ) * Jc N (δ⁻¹ • x) := by
  simp [Jδ]

/-- Convolution by the even kernel on Schwartz tests. -/
def SδSchwartz (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) :=
  SchwartzMap.convolution (lsmul ℂ ℂ) (Jδ N δ hδ)

/-- Reflection of a Schwartz kernel. -/
def reflectedSchwartz {N : ℕ} (K : 𝓢(Carrier N, ℂ)) : 𝓢(Carrier N, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) K

/-- The test-function operator used to define convolution of a tempered distribution. -/
def temperedConvolutionTests {N : ℕ} (K : 𝓢(Carrier N, ℂ)) :
    𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ) :=
  SchwartzMap.convolution (lsmul ℂ ℂ) (reflectedSchwartz K)

/-- Convolution of a tempered distribution by a Schwartz kernel, defined by transposition. -/
def temperedConvolution {N : ℕ} (T : 𝓢'(Carrier N, ℂ)) (K : 𝓢(Carrier N, ℂ)) :
    𝓢'(Carrier N, ℂ) :=
  PointwiseConvergenceCLM.precomp _ (temperedConvolutionTests K) T

/-- [BB.Def5.18] The pairing identity defining convolution by a Schwartz kernel. -/
@[simp] theorem temperedConvolution_apply {N : ℕ} (T : 𝓢'(Carrier N, ℂ))
    (K ψ : 𝓢(Carrier N, ℂ)) :
    temperedConvolution T K ψ = T (temperedConvolutionTests K ψ) := rfl

/-- On Schwartz functions the regularizer is the usual convolution with its kernel. -/
theorem SδSchwartz_eq_convolution (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (ψ : 𝓢(Carrier N, ℂ)) :
    SδSchwartz N δ hδ ψ =
      SchwartzMap.convolution (lsmul ℂ ℂ) ψ (Jδ N δ hδ) := by
  change SchwartzMap.convolution (lsmul ℂ ℂ) (Jδ N δ hδ) ψ = _
  rw [← SchwartzMap.convolution_flip (lsmul ℂ ℂ) ψ (Jδ N δ hδ)]
  have hflip : (lsmul ℂ ℂ).flip = lsmul ℂ ℂ := by
    ext
    simp [lsmul]
  rw [hflip]

/-- Pointwise, the Schwartz regularizer is the ordinary function convolution. -/
theorem SδSchwartz_apply_eq_convolution (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (ψ : 𝓢(Carrier N, ℂ)) (x : Carrier N) :
    SδSchwartz N δ hδ ψ x = (ψ ⋆[lsmul ℂ ℂ] Jδ N δ hδ) x := by
  rw [SδSchwartz_eq_convolution]
  exact SchwartzMap.convolution_apply (lsmul ℂ ℂ) ψ (Jδ N δ hδ) x

/-- The transpose convolution of a tempered distribution with `Jδ`. -/
def Sδ (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (T : 𝓢'(Carrier N, ℂ)) :
    𝓢'(Carrier N, ℂ) :=
  temperedConvolution T (Jδ N δ hδ)

end Hormander.A
