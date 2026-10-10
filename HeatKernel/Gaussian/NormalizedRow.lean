-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Normalized local kernel rows

Dividing a restricted row by its local square norm gives unit square integral.
Pairing this datum with the original row recovers that norm exactly.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
namespace HeatKernel.Gaussian

/-- A restricted row normalized by its nonzero square norm has square integral one. -/
theorem integral_sq_normalized_indicator_eq_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S) (f : α → ℝ)
    (hpos : 0 < ∫ x in S, f x ^ 2 ∂μ) :
    (∫ x, (S.indicator (fun x ↦ f x / Real.sqrt (∫ z in S, f z ^ 2 ∂μ)) x) ^ 2 ∂μ) = 1 := by
  have heq : (fun x ↦ (S.indicator (fun x ↦ f x /
      Real.sqrt (∫ z in S, f z ^ 2 ∂μ)) x) ^ 2) =
      S.indicator (fun x ↦ f x ^ 2 / (∫ z in S, f z ^ 2 ∂μ)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, div_pow, Real.sq_sqrt hpos.le]
    · simp [hx]
  rw [heq, integral_indicator hS, integral_div]
  exact div_self hpos.ne'

/-- Pairing a normalized restricted row with the row gives its square norm. -/
theorem integral_mul_normalized_indicator_eq_sqrt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S) (f : α → ℝ)
    (hpos : 0 < ∫ x in S, f x ^ 2 ∂μ) :
    (∫ x, f x * S.indicator (fun x ↦ f x / Real.sqrt (∫ z in S, f z ^ 2 ∂μ)) x ∂μ) =
      Real.sqrt (∫ z in S, f z ^ 2 ∂μ) := by
  have heq : (fun x ↦ f x * S.indicator (fun x ↦ f x /
      Real.sqrt (∫ z in S, f z ^ 2 ∂μ)) x) =
      S.indicator (fun x ↦ f x ^ 2 / Real.sqrt (∫ z in S, f z ^ 2 ∂μ)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx]; ring
    · simp [hx]
  rw [heq, integral_indicator hS, integral_div]
  apply (div_eq_iff (Real.sqrt_pos.mpr hpos).ne').mpr
  exact (Real.mul_self_sqrt hpos.le).symm

/-- A measurable row with positive local square integral gives a square-integrable
normalized datum. -/
theorem memLp_normalized_indicator {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) (hpos : 0 < ∫ x in S, f x ^ 2 ∂μ) :
    MemLp (S.indicator (fun x ↦ f x / Real.sqrt (∫ z in S, f z ^ 2 ∂μ))) 2 μ := by
  apply (memLp_two_iff_integrable_sq (((hf.aemeasurable.div_const _).aestronglyMeasurable).indicator hS)).mpr
  apply Integrable.of_integral_ne_zero
  rw [integral_sq_normalized_indicator_eq_one μ hS f hpos]
  exact one_ne_zero

end HeatKernel.Gaussian
