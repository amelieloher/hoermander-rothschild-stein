-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! Squaring an L² Poincaré estimate gives its extended integral formulation. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace HeatKernel.Sobolev

/-- The square of the L² seminorm of a real function is its quadratic moment. -/
theorem eLpNorm_two_sq_eq_lintegral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f : A → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  simp_rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] at h
  exact h

/-- A seminorm estimate with coefficient C r yields a quadratic moment estimate
with coefficient C² r², including infinite moments. -/
theorem lintegral_sq_le_of_eLpNorm_two_le {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f g : A → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    {C r : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal (C * r) * eLpNorm g 2 μ) :
    (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ≤
      ENNReal.ofReal (C ^ 2) * ENNReal.ofReal r ^ 2 *
        ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ := by
  have hs := pow_le_pow_left' h 2
  rw [eLpNorm_two_sq_eq_lintegral hf, mul_pow,
    ENNReal.ofReal_mul hC, mul_pow, ← ENNReal.ofReal_pow hC,
    eLpNorm_two_sq_eq_lintegral hg] at hs
  exact hs

end HeatKernel.Sobolev
