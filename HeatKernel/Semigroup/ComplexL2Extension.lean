-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ComplexL2Components

/-! # Complex extension of real L² operators

The extension acts separately on real and imaginary parts. Commutation with multiplication
by the imaginary unit upgrades the bounded real-linear extension to a complex-linear map.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The componentwise extension, first viewed as a bounded real-linear map. -/
def realL2Extension (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  (l2OfReal μ).comp (R.comp (l2RealPart μ)) +
    Complex.I • (l2OfReal μ).comp (R.comp (l2ImaginaryPart μ))

theorem realL2Extension_apply (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    realL2Extension μ R f = l2OfReal μ (R (l2RealPart μ f)) +
      Complex.I • l2OfReal μ (R (l2ImaginaryPart μ f)) := rfl

theorem realL2Extension_I_smul (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    realL2Extension μ R (Complex.I • f) = Complex.I • realL2Extension μ R f := by
  simp only [realL2Extension_apply, l2RealPart_I_smul, l2ImaginaryPart_I_smul,
    map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem map_complex_smul_of_map_I {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℝ] F) (hI : ∀ x, T (Complex.I • x) = Complex.I • T x)
    (c : ℂ) (x : E) : T (c • x) = c • T x := by
  rw [← Complex.re_add_im c]
  simp only [add_smul, mul_smul, Complex.coe_smul, map_add, T.map_smul, hI]

/-- The bounded complex-linear extension of an operator on real L². -/
def complexL2Extension (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ where
  __ := realL2Extension μ R
  map_smul' := map_complex_smul_of_map_I _ (realL2Extension_I_smul μ R)

@[simp] theorem complexL2Extension_apply (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    complexL2Extension μ R f = l2OfReal μ (R (l2RealPart μ f)) +
      Complex.I • l2OfReal μ (R (l2ImaginaryPart μ f)) := rfl

@[simp] theorem complexL2Extension_ofReal (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 μ) :
    complexL2Extension μ R (l2OfReal μ f) = l2OfReal μ (R f) := by
  simp

@[simp] theorem l2RealPart_complexL2Extension (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (f : Lp ℂ 2 μ) : l2RealPart μ (complexL2Extension μ R f) = R (l2RealPart μ f) := by
  simp only [complexL2Extension_apply, map_add, l2RealPart_ofReal,
    l2RealPart_I_smul, l2ImaginaryPart_ofReal, neg_zero, add_zero]

@[simp] theorem l2ImaginaryPart_complexL2Extension (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (f : Lp ℂ 2 μ) : l2ImaginaryPart μ (complexL2Extension μ R f) = R (l2ImaginaryPart μ f) := by
  simp only [complexL2Extension_apply, map_add, l2ImaginaryPart_ofReal,
    l2ImaginaryPart_I_smul, l2RealPart_ofReal, zero_add]

theorem complexL2Extension_injective (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : Function.Injective R) : Function.Injective (complexL2Extension μ R) := by
  intro f g hfg
  have hr := congrArg (l2RealPart μ) hfg
  have hi := congrArg (l2ImaginaryPart μ) hfg
  simp only [l2RealPart_complexL2Extension] at hr
  simp only [l2ImaginaryPart_complexL2Extension] at hi
  calc
    f = l2OfReal μ (l2RealPart μ f) + Complex.I • l2OfReal μ (l2ImaginaryPart μ f) :=
      (l2OfReal_realPart_add_I_imaginaryPart μ f).symm
    _ = l2OfReal μ (l2RealPart μ g) + Complex.I • l2OfReal μ (l2ImaginaryPart μ g) := by
      rw [hR hr, hR hi]
    _ = g := l2OfReal_realPart_add_I_imaginaryPart μ g

theorem norm_complexL2Extension_le_one (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hR : ‖R‖ ≤ 1) :
    ‖complexL2Extension μ R‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have hbound (g : Lp ℝ 2 μ) : ‖R g‖ ≤ ‖g‖ := by
    exact (R.le_opNorm g).trans (by simpa using (mul_le_mul_of_nonneg_right hR (norm_nonneg g)))
  have hreal := hbound (l2RealPart μ f)
  have himag := hbound (l2ImaginaryPart μ f)
  have hid := norm_sq_eq_realPart_add_imaginaryPart μ f
  have heq : ‖complexL2Extension μ R f‖ ^ 2 =
      ‖R (l2RealPart μ f)‖ ^ 2 + ‖R (l2ImaginaryPart μ f)‖ ^ 2 := by
    rw [complexL2Extension_apply, norm_l2OfReal_add_I_sq]
  simp only [one_mul]
  nlinarith [norm_nonneg (R (l2RealPart μ f)), norm_nonneg (R (l2ImaginaryPart μ f)),
    norm_nonneg (l2RealPart μ f), norm_nonneg (l2ImaginaryPart μ f),
    norm_nonneg f, norm_nonneg (complexL2Extension μ R f)]

end HeatKernel
