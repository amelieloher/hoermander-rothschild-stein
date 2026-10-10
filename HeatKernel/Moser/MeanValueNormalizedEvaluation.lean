-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueContinuousEvaluation
public import HeatKernel.Sobolev.QuadraticPoincareConversion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Squared pointwise bounds from normalized quadratic means -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel

/-- The real square of the extended quadratic norm is the ordinary quadratic integral. -/
theorem eLpNorm_two_toReal_sq_eq_integral_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  have h := congrArg ENNReal.toReal (Sobolev.eLpNorm_two_sq_eq_lintegral hf)
  rw [ENNReal.toReal_pow] at h
  exact h.trans (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
    (hf.aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable).symm

/-- Scaling by the inverse volume gives exactly the normalized quadratic moment. -/
theorem eLpNorm_two_normalized_toReal_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {V : ℝ} (hV : 0 < V) :
    (eLpNorm f 2 (ENNReal.ofReal V⁻¹ • μ)).toReal ^ 2 =
      (∫ x, f x ^ 2 ∂μ) / V := by
  rw [eLpNorm_two_toReal_sq_eq_integral_sq _ (hf.smul_measure _), integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hV.le), smul_eq_mul]
  ring

/-- A normalized essential quadratic bound controls each continuous point value in
its ordinary squared-integral form. The essential mean-value bound is an explicit input. -/
theorem sq_le_normalized_integral_of_essential_bound
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ ν : Measure α) [μ.IsOpenPosMeasure] {U : Set α} (hU : IsOpen U)
    {f : α → ℝ} (hf : ContinuousOn f U) (hmem : MemLp f 2 ν)
    {C V : ℝ} (hC : 0 ≤ C) (hV : 0 < V)
    (hbound : eLpNormEssSup f (μ.restrict U) ≤
      ENNReal.ofReal C * eLpNorm f 2 (ENNReal.ofReal V⁻¹ • ν)) :
    ∀ x ∈ U, f x ^ 2 ≤ C ^ 2 / V * (∫ y, f y ^ 2 ∂ν) := by
  have hnorm := hmem.smul_measure (c := ENNReal.ofReal V⁻¹) ENNReal.ofReal_ne_top
  have hreal : eLpNormEssSup f (μ.restrict U) ≤
      ENNReal.ofReal (C * (eLpNorm f 2 (ENNReal.ofReal V⁻¹ • ν)).toReal) := by
    rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hnorm.eLpNorm_ne_top]
    exact hbound
  have hsq := sq_le_of_eLpNormEssSup_le_of_continuousOn (μ := μ) hU hf
    (mul_nonneg hC ENNReal.toReal_nonneg) hreal
  intro x hx
  have h := hsq x hx
  rw [mul_pow, eLpNorm_two_normalized_toReal_sq ν hmem.aestronglyMeasurable hV] at h
  convert h using 1; ring

end HeatKernel
