-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeightedTaylorRemainder

/-! # Integrability of nonlinear energies and their linear variations

A nonlinearity with Lipschitz derivative vanishing together with its derivative at zero
has integrable weighted energy on L². Its weighted derivative belongs to L² as well.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- A scalar nonlinearity vanishing to first order at zero has integrable weighted energy
for every square integrable function and bounded measurable weight. -/
theorem integrable_weighted_nonlinearity_of_lipschitz_deriv {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (v : Lp ℝ 2 μ) :
    Integrable (fun x => ψ x * Φ (v x)) μ := by
  have H := (integrable_and_norm_integral_weighted_taylor_remainder hΦ hL
    (v := fun _ : α => (0 : ℝ)) aestronglyMeasurable_const hψ hA hb v).1
  simpa only [zero_add, hzero, hdzero, zero_mul, sub_zero] using H

/-- A Lipschitz scalar derivative vanishing at zero, multiplied by a bounded measurable
weight, gives a square integrable coefficient for the linear energy variation. -/
theorem memLp_weighted_deriv_of_lipschitz_deriv {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (deriv Φ)) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (v : Lp ℝ 2 μ) :
    MemLp (fun x => ψ x * deriv Φ (v x)) 2 μ := by
  have hm := hψ.mul (hL.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
  apply (Lp.memLp v).of_le_mul hm (c := A * L)
  filter_upwards [hb] with x hx
  have hd : ‖deriv Φ (v x)‖ ≤ (L : ℝ) * ‖v x‖ := by
    simpa only [hdzero, sub_zero] using hL.norm_sub_le (v x) 0
  calc
    ‖ψ x * deriv Φ (v x)‖ = ‖ψ x‖ * ‖deriv Φ (v x)‖ := norm_mul _ _
    _ ≤ A * ((L : ℝ) * ‖v x‖) := mul_le_mul hx hd (norm_nonneg _) hA
    _ = (A * L) * ‖v x‖ := by ring

end HeatKernel
