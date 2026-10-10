-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.NormalizedRow
public import HeatKernel.Gaussian.TruncatedDistance
import Mathlib.Tactic

/-! # Weighted energy of normalized local data

A bounded logarithmic weight preserves integrability of normalized square data.
Its bound on the support gives the sharper initial weighted energy estimate.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
namespace HeatKernel.Gaussian

/-- A bounded weight on the support controls the weighted square integral of
normalized local data by the exponential of that bound. -/
theorem integral_weighted_sq_normalized_indicator_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S) (f ψ : α → ℝ)
    (hpos : 0 < ∫ z in S, f z ^ 2 ∂μ) (hψ : AEStronglyMeasurable ψ μ)
    {B L : ℝ} (hglobal : ∀ x, ψ x ≤ B) (hlocal : ∀ x ∈ S, ψ x ≤ L) :
    (∫ x, Real.exp (ψ x) *
      (S.indicator (fun z ↦ f z / Real.sqrt (∫ w in S, f w ^ 2 ∂μ)) x) ^ 2 ∂μ) ≤
        Real.exp L := by
  let g := S.indicator (fun z ↦ f z / Real.sqrt (∫ w in S, f w ^ 2 ∂μ))
  have hunit : (∫ x, g x ^ 2 ∂μ) = 1 :=
    integral_sq_normalized_indicator_eq_one μ hS f hpos
  have hi : Integrable (fun x ↦ g x ^ 2) μ := Integrable.of_integral_ne_zero (by rw [hunit]; norm_num)
  have hw : Integrable (fun x ↦ Real.exp (ψ x) * g x ^ 2) μ := by
    apply hi.bdd_mul (Real.continuous_exp.comp_aestronglyMeasurable hψ)
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (hglobal x))
  calc
    _ ≤ ∫ x, Real.exp L * g x ^ 2 ∂μ := by
      apply integral_mono_ae hw (hi.const_mul _)
      apply Filter.Eventually.of_forall
      intro x
      by_cases hx : x ∈ S
      · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hlocal x hx)) (sq_nonneg _)
      · simp [g, hx]
    _ = Real.exp L := by rw [integral_const_mul, hunit, mul_one]

end HeatKernel.Gaussian
