-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.QuadraticAverage
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Quadratic oscillation about a normalized set average -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel.Sobolev

/-- Squared distance to a set average is bounded by the pointwise and averaged
squared distances to any fixed constant. -/
theorem sq_sub_setAverage_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {U : Set α} (hU : MeasurableSet U) (hUpos : 0 < μ.real U)
    {f : α → ℝ} (hf : IntegrableOn f U μ)
    (hf₂ : IntegrableOn (fun x => f x ^ 2) U μ) (z c : ℝ) :
    (z - (∫ x in U, f x ∂μ) / μ.real U) ^ 2 ≤
      2 * (z - c) ^ 2 + 2 / μ.real U * ∫ x in U, (f x - c) ^ 2 ∂μ := by
  have hfinite : μ U ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hUpos).2.ne
  let w : α → ℝ := U.indicator (fun _ => (μ.real U)⁻¹)
  have hint (g : α → ℝ) : (fun x => w x * g x) =
      U.indicator (fun x => (μ.real U)⁻¹ * g x) := by
    funext x
    by_cases hx : x ∈ U <;> simp [w, hx]
  have hw : Integrable w μ :=
    (integrable_indicator_iff hU).mpr (integrableOn_const hfinite)
  have hwf : Integrable (fun x => w x * f x) μ := by
    rw [hint f]
    exact (integrable_indicator_iff hU).mpr (hf.const_mul _)
  have hwf₂ : Integrable (fun x => w x * f x ^ 2) μ := by
    rw [hint (fun x => f x ^ 2)]
    exact (integrable_indicator_iff hU).mpr (hf₂.const_mul _)
  have hw₀ : 0 ≤ᵐ[μ] w := Filter.Eventually.of_forall (fun x => by
    by_cases hx : x ∈ U
    · simp only [w, indicator_of_mem hx]
      exact inv_nonneg.mpr hUpos.le
    · simp [w, hx])
  have hmass : (∫ x, w x ∂μ) = 1 := by
    rw [show w = U.indicator (fun _ => (μ.real U)⁻¹) from rfl,
      integral_indicator hU, setIntegral_const, smul_eq_mul]
    exact mul_inv_cancel₀ hUpos.ne'
  have H := sq_sub_integral_weight_mul_le hw hwf hwf₂ hw₀ hmass z c
  rw [hint f, hint (fun x => (f x - c) ^ 2), integral_indicator hU,
    integral_const_mul, integral_indicator hU, integral_const_mul] at H
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm (μ.real U)⁻¹] using H

end HeatKernel.Sobolev
