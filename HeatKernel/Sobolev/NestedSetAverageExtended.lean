-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NestedSetAverages
import Mathlib.Tactic

/-! # Nonnegative oscillation bounds for nested set averages -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- The nested-average oscillation bound in nonnegative integral form. -/
theorem lintegral_sub_nested_setAverage_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {U V : Set α} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUV : U ⊆ V) (hVfinite : μ V ≠ ⊤) (hUpos : 0 < μ.real U)
    {u : α → ℝ} (hu : IntegrableOn u V μ)
    (hu₂ : IntegrableOn (fun x => u x ^ 2) V μ) :
    (∫⁻ x in V, ENNReal.ofReal ((u x - (∫ y in U, u y ∂μ) / μ.real U) ^ 2) ∂μ) ≤
      ENNReal.ofReal (1 + μ.real V / μ.real U) *
        ∫⁻ x in V, ENNReal.ofReal ((u x - (∫ y in V, u y ∂μ) / μ.real V) ^ 2) ∂μ := by
  have hvar (c : ℝ) : IntegrableOn (fun x => (u x - c) ^ 2) V μ := by
    convert (hu₂.sub (hu.mul_const (2 * c))).add
      ((integrableOn_const hVfinite : IntegrableOn (fun _ : α => (1 : ℝ)) V μ).mul_const (c ^ 2)) using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, one_mul]
    ring
  have hI (c : ℝ) := ofReal_integral_eq_lintegral_ofReal
    (f := fun x => (u x - c) ^ 2) (hvar c)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  rw [← hI, ← hI, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + μ.real V / μ.real U)]
  exact ENNReal.ofReal_le_ofReal
    (integral_sub_nested_setAverage_sq_le hU hV hUV hVfinite hUpos hu hu₂)

/-- Poincaré on the larger set controls oscillation about the smaller set's average. -/
theorem lintegral_sub_nested_setAverage_sq_le_of_poincare
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {U V : Set α}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V)
    (hVfinite : μ V ≠ ⊤) (hUpos : 0 < μ.real U)
    {u : α → ℝ} (hu : IntegrableOn u V μ)
    (hu₂ : IntegrableOn (fun x => u x ^ 2) V μ)
    {P R : ℝ≥0∞} {g : α → ℝ≥0∞}
    (hratio : ENNReal.ofReal (1 + μ.real V / μ.real U) ≤ R)
    (hpoincare : (∫⁻ x in V, ENNReal.ofReal
      ((u x - (∫ y in V, u y ∂μ) / μ.real V) ^ 2) ∂μ) ≤ P * ∫⁻ x in V, g x ∂μ) :
    (∫⁻ x in V, ENNReal.ofReal ((u x - (∫ y in U, u y ∂μ) / μ.real U) ^ 2) ∂μ) ≤
      R * P * ∫⁻ x in V, g x ∂μ := by
  apply (lintegral_sub_nested_setAverage_sq_le hU hV hUV hVfinite hUpos hu hu₂).trans
  calc
    _ ≤ R * (P * ∫⁻ x in V, g x ∂μ) := mul_le_mul hratio hpoincare (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc]

end HeatKernel.Sobolev
