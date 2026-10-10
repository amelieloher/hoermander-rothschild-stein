-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueBoundedPowerDerivatives
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-! # Removing bounded-power truncations in integral estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- Uniform integral bounds for bounded positive powers pass to the full positive power. -/
theorem lintegral_rpow_le_of_boundedPositivePower_bounds
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {u : α → ℝ}
    (hu : AEMeasurable u μ) (hnonneg : ∀ᵐ x ∂μ, 0 ≤ u x)
    {γ : ℝ} (hγ : 1 ≤ γ) {K : ℝ≥0∞}
    (hbound : ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal (boundedPositivePower ((n : ℝ) + 1) γ (u x)) ∂μ) ≤ K) :
    (∫⁻ x, ENNReal.ofReal ((u x) ^ γ) ∂μ) ≤ K := by
  have hm (n : ℕ) : AEMeasurable
      (fun x => ENNReal.ofReal (boundedPositivePower ((n : ℝ) + 1) γ (u x))) μ := by
    have hc := (lipschitzWith_boundedPositivePower
      (M := (n : ℝ) + 1) (by positivity) hγ).continuous
    exact (hc.measurable.comp_aemeasurable hu).ennreal_ofReal
  have hlim : (fun x => liminf
      (fun n : ℕ => ENNReal.ofReal (boundedPositivePower ((n : ℝ) + 1) γ (u x))) atTop)
      =ᵐ[μ] fun x => ENNReal.ofReal ((u x) ^ γ) := by
    filter_upwards [hnonneg] with x hx
    have he : (fun n : ℕ => ENNReal.ofReal
        (boundedPositivePower ((n : ℝ) + 1) γ (u x))) =ᶠ[atTop]
        (fun _ => ENNReal.ofReal ((u x) ^ γ)) :=
      (eventually_boundedPositivePower_eq_rpow (γ := γ) hx).mono fun _ h => congrArg _ h
    exact (tendsto_const_nhds.congr' he.symm).liminf_eq
  calc
    _ = ∫⁻ x, liminf
        (fun n : ℕ => ENNReal.ofReal (boundedPositivePower ((n : ℝ) + 1) γ (u x))) atTop ∂μ :=
      (lintegral_congr_ae hlim).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ x,
        ENNReal.ofReal (boundedPositivePower ((n : ℝ) + 1) γ (u x)) ∂μ) atTop :=
      lintegral_liminf_le' hm
    _ ≤ K := le_trans (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault))
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hbound))

end HeatKernel
