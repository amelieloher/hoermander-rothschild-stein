-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

noncomputable section

open LineDeriv MeasureTheory Real SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace

namespace Hormander.A

/-- The Euclidean carrier used by the Fourier and Sobolev modules. -/
abbrev Carrier (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Fourier inversion makes the Schwartz Fourier transform bijective. -/
theorem fourier_schwartz_bijective {N : ℕ} :
    Function.Bijective
      (SchwartzMap.fourierTransformCLM ℂ :
        𝓢(Carrier N, ℂ) →L[ℂ] 𝓢(Carrier N, ℂ)) := by
  constructor
  · intro φ ψ h
    have hfourier : 𝓕 φ = 𝓕 ψ := by
      simpa [SchwartzMap.fourierTransformCLM_apply] using h
    have hinv := congrArg (fun f : 𝓢(Carrier N, ℂ) => 𝓕⁻ f) hfourier
    simpa using hinv
  · intro ψ
    refine ⟨𝓕⁻ ψ, ?_⟩
    simp [SchwartzMap.fourierTransformCLM_apply]

/-- The Fourier transform of a Schwartz line derivative is multiplication by its symbol. -/
theorem fourier_schwartz_lineDeriv {N : ℕ} (φ : 𝓢(Carrier N, ℂ)) (v : Carrier N) :
    𝓕 (∂_{v} φ) =
      (2 * π * Complex.I) •
        smulLeftCLM ℂ (inner ℝ · v) (𝓕 φ) := by
  exact SchwartzMap.fourier_lineDerivOp_eq φ v

/-- Plancherel's identity for complex Schwartz functions. -/
theorem fourier_schwartz_plancherel {N : ℕ} (φ ψ : 𝓢(Carrier N, ℂ)) :
    ∫ ξ, ⟪𝓕 φ ξ, 𝓕 ψ ξ⟫ = ∫ x, ⟪φ x, ψ x⟫ := by
  exact SchwartzMap.integral_inner_fourier_fourier φ ψ

/-- The inverse Fourier transform is the Fourier transform followed by reflection. -/
theorem fourierInv_eq_fourier_neg {N : ℕ} (f : Carrier N → ℂ) (ξ : Carrier N) :
    𝓕⁻ f ξ = 𝓕 f (-ξ) := by
  exact Real.fourierInv_eq_fourier_neg f ξ

/-- The tempered-distribution Fourier transform is defined by transposition. -/
theorem tempered_fourier_apply {N : ℕ} (T : 𝓢'(Carrier N, ℂ))
    (φ : 𝓢(Carrier N, ℂ)) :
    𝓕 T φ = T (𝓕 φ) := by
  exact TemperedDistribution.fourier_apply T φ

/-- Fourier inversion holds on complex tempered distributions. -/
theorem tempered_fourier_inversion {N : ℕ} (T : 𝓢'(Carrier N, ℂ)) :
    𝓕⁻ (𝓕 T) = T ∧ 𝓕 (𝓕⁻ T) = T := by
  constructor <;> simp

end Hormander.A
