-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Hormander.A.Fourier
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform Convolution

namespace Hormander.B

theorem fourier_fourier_apply {N : ℕ} (g : TestFunction N) (x : Carrier N) :
    𝓕 (𝓕 g) x = g (-x) := by
  have h1 : 𝓕⁻ (𝓕 g) = g := FourierTransform.fourierInv_fourier_eq g
  have h2 := Hormander.A.fourierInv_eq_fourier_neg (fun y => 𝓕 g y) (-x)
  rw [neg_neg] at h2
  have h3 : (𝓕⁻ (𝓕 g)) (-x) = 𝓕⁻ (fun y => 𝓕 g y) (-x) := by
    rw [SchwartzMap.fourierInv_coe]
  rw [h1] at h3
  rw [h3, h2, SchwartzMap.fourier_coe]


/-- The Fourier transform of a product of Schwartz functions is the convolution of their Fourier
transforms. -/
theorem fourier_mul_apply {N : ℕ} (g u : TestFunction N) (ξ : Carrier N) :
    𝓕 (multiplierOperator g u) ξ = ∫ a, 𝓕 g a * 𝓕 u (ξ - a) := by
  set C := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g) (𝓕 u) with hC
  have hw : ∀ x, multiplierOperator g u x = g x * u x := fun x => by
    show (SchwartzMap.smulLeftCLM ℂ g u) x = g x * u x
    rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
    rfl
  have hCw : 𝓕 C = 𝓕 (𝓕 (multiplierOperator g u)) := by
    ext x
    rw [hC, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      fourier_fourier_apply, fourier_fourier_apply, fourier_fourier_apply, hw]
    rfl
  have hinj : Function.Injective (𝓕 : TestFunction N → TestFunction N) :=
    (Hormander.A.fourier_schwartz_bijective (N := N)).1
  have hC' : C = 𝓕 (multiplierOperator g u) := hinj hCw
  rw [← hC', hC, SchwartzMap.convolution_apply]
  rfl

end Hormander.B
