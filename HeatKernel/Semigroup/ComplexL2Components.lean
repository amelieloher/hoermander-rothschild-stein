-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Real and imaginary components of complex L²

Composition with the scalar real and imaginary projections gives the concrete maps needed
to extend real L² operators to complex L².
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The real component of a complex L² vector. -/
def l2RealPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ

/-- The imaginary component of a complex L² vector. -/
def l2ImaginaryPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.imCLM.compLpL 2 μ

/-- The canonical embedding of real L² into complex L². -/
def l2OfReal : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

theorem coeFn_l2RealPart (f : Lp ℂ 2 μ) :
    l2RealPart μ f =ᵐ[μ] fun x => (f x).re := Complex.reCLM.coeFn_compLpL f

theorem coeFn_l2ImaginaryPart (f : Lp ℂ 2 μ) :
    l2ImaginaryPart μ f =ᵐ[μ] fun x => (f x).im := Complex.imCLM.coeFn_compLpL f

theorem coeFn_l2OfReal (f : Lp ℝ 2 μ) :
    l2OfReal μ f =ᵐ[μ] fun x => (f x : ℂ) := Complex.ofRealCLM.coeFn_compLpL f

@[simp] theorem l2RealPart_ofReal (f : Lp ℝ 2 μ) : l2RealPart μ (l2OfReal μ f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_l2RealPart μ (l2OfReal μ f), coeFn_l2OfReal μ f] with x hr hf
  simp only [hr, hf, Complex.ofReal_re]

@[simp] theorem l2ImaginaryPart_ofReal (f : Lp ℝ 2 μ) : l2ImaginaryPart μ (l2OfReal μ f) = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_l2ImaginaryPart μ (l2OfReal μ f), coeFn_l2OfReal μ f,
    Lp.coeFn_zero ℝ 2 μ] with x hi hf hz
  simp only [hi, hf, Complex.ofReal_im, hz, Pi.zero_apply]

theorem l2OfReal_realPart_add_I_imaginaryPart (f : Lp ℂ 2 μ) :
    l2OfReal μ (l2RealPart μ f) + Complex.I • l2OfReal μ (l2ImaginaryPart μ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (l2OfReal μ (l2RealPart μ f))
      (Complex.I • l2OfReal μ (l2ImaginaryPart μ f)),
    Lp.coeFn_smul Complex.I (l2OfReal μ (l2ImaginaryPart μ f)),
    coeFn_l2OfReal μ (l2RealPart μ f), coeFn_l2OfReal μ (l2ImaginaryPart μ f),
    coeFn_l2RealPart μ f, coeFn_l2ImaginaryPart μ f] with x ha hs hor hoi hr hi
  simp only [ha, hs, hor, hoi, hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using Complex.re_add_im (f x)

theorem l2RealPart_I_smul (f : Lp ℂ 2 μ) : l2RealPart μ (Complex.I • f) = -l2ImaginaryPart μ f := by
  apply Lp.ext
  filter_upwards [coeFn_l2RealPart μ (Complex.I • f), Lp.coeFn_smul Complex.I f,
    Lp.coeFn_neg (l2ImaginaryPart μ f), coeFn_l2ImaginaryPart μ f] with x hr hs hn hi
  rw [hr, hn]
  simp [hs, hi, Complex.mul_re]

theorem l2ImaginaryPart_I_smul (f : Lp ℂ 2 μ) : l2ImaginaryPart μ (Complex.I • f) = l2RealPart μ f := by
  apply Lp.ext
  filter_upwards [coeFn_l2ImaginaryPart μ (Complex.I • f), Lp.coeFn_smul Complex.I f,
    coeFn_l2RealPart μ f] with x hi hs hr
  simp [hi, hs, hr, Complex.mul_im]

theorem inner_l2OfReal (f g : Lp ℝ 2 μ) :
    inner ℂ (l2OfReal μ f) (l2OfReal μ g) = (inner ℝ f g : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [coeFn_l2OfReal μ f, coeFn_l2OfReal μ g] with x hf hg
  simp [hf, hg]

theorem norm_l2OfReal (f : Lp ℝ 2 μ) : ‖l2OfReal μ f‖ = ‖f‖ := by
  have h : ‖l2OfReal μ f‖ ^ 2 = ‖f‖ ^ 2 := by
    calc
      ‖l2OfReal μ f‖ ^ 2 = (inner ℂ (l2OfReal μ f) (l2OfReal μ f)).re := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = inner ℝ f f := by rw [inner_l2OfReal, Complex.ofReal_re]
      _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  nlinarith [norm_nonneg f, norm_nonneg (l2OfReal μ f)]

theorem norm_l2OfReal_add_I_sq (f g : Lp ℝ 2 μ) :
    ‖l2OfReal μ f + Complex.I • l2OfReal μ g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, inner_l2OfReal, norm_smul]
  simp [norm_l2OfReal]

theorem norm_sq_eq_realPart_add_imaginaryPart (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ‖l2RealPart μ f‖ ^ 2 + ‖l2ImaginaryPart μ f‖ ^ 2 := by
  rw [← norm_l2OfReal_add_I_sq, l2OfReal_realPart_add_I_imaginaryPart]

end HeatKernel
