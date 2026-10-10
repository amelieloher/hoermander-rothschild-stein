-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ComplexL2Extension
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Positivity of the complex extension

The complex inner product separates into the real component pairings. Consequently a
positive symmetric real operator has a positive self-adjoint complex extension.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem inner_l2OfReal_add_I (a b c d : Lp ℝ 2 μ) :
    inner ℂ (l2OfReal μ a + Complex.I • l2OfReal μ b)
      (l2OfReal μ c + Complex.I • l2OfReal μ d) =
      ((inner ℝ a c + inner ℝ b d : ℝ) : ℂ) +
        Complex.I * ((inner ℝ a d - inner ℝ b c : ℝ) : ℂ) := by
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_l2OfReal, Complex.ofReal_add, Complex.ofReal_sub, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inner_complexL2Extension (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f g : Lp ℂ 2 μ) :
    inner ℂ (complexL2Extension μ R f) g =
      ((inner ℝ (R (l2RealPart μ f)) (l2RealPart μ g) +
        inner ℝ (R (l2ImaginaryPart μ f)) (l2ImaginaryPart μ g) : ℝ) : ℂ) +
      Complex.I * ((inner ℝ (R (l2RealPart μ f)) (l2ImaginaryPart μ g) -
        inner ℝ (R (l2ImaginaryPart μ f)) (l2RealPart μ g) : ℝ) : ℂ) := by
  conv_lhs => arg 3; rw [← l2OfReal_realPart_add_I_imaginaryPart μ g]
  rw [complexL2Extension_apply, inner_l2OfReal_add_I]

theorem complexL2Extension_isSelfAdjoint (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : IsSelfAdjoint R) : IsSelfAdjoint (complexL2Extension μ R) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hs (a b : Lp ℝ 2 μ) : inner ℝ (R a) b = inner ℝ a (R b) := hR.isSymmetric a b
  change inner ℂ (complexL2Extension μ R f) g = inner ℂ f (complexL2Extension μ R g)
  rw [inner_complexL2Extension]
  conv_rhs => arg 2; rw [← l2OfReal_realPart_add_I_imaginaryPart μ f]
  rw [complexL2Extension_apply, inner_l2OfReal_add_I]
  simp only [hs]

theorem complexL2Extension_isPositive (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : R.IsPositive) : (complexL2Extension μ R).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨complexL2Extension_isSelfAdjoint μ R hR.isSelfAdjoint, ?_⟩
  intro f
  change 0 ≤ (inner ℂ (complexL2Extension μ R f) f).re
  rw [inner_complexL2Extension]
  simpa using add_nonneg (hR.re_inner_nonneg_left (l2RealPart μ f))
    (hR.re_inner_nonneg_left (l2ImaginaryPart μ f))

theorem denseRange_complexL2Extension (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : IsSelfAdjoint R) (hinj : Function.Injective R) :
    DenseRange (complexL2Extension μ R) := by
  change Dense ((complexL2Extension μ R).range : Set (Lp ℂ 2 μ))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    (complexL2Extension μ R).orthogonal_range]
  rw [(complexL2Extension_isSelfAdjoint μ R hR).adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr (complexL2Extension_injective μ R hinj)

end HeatKernel
