-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.IntegratedQuadraticRemainder

/-! # Weighted scalar Taylor errors in square integrable increments

A bounded spatial weight and a Lipschitz scalar derivative give an integrable quadratic
error, even when the base function is only measurable.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- The weighted nonlinear Taylor error is integrable and bounded by the squared L² increment.
Only measurability of the base function is needed for this error estimate. -/
theorem integrable_and_norm_integral_weighted_taylor_remainder {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    {v ψ : α → ℝ} (hv : AEStronglyMeasurable v μ) (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (k : Lp ℝ 2 μ) :
    Integrable (fun x => ψ x * (Φ (v x + k x) - Φ (v x) - deriv Φ (v x) * k x)) μ ∧
      ‖∫ x, ψ x * (Φ (v x + k x) - Φ (v x) - deriv Φ (v x) * k x) ∂μ‖ ≤
        (A * L) * ‖k‖ ^ 2 := by
  have hk := Lp.aestronglyMeasurable k
  have hr : AEStronglyMeasurable
      (fun x => ψ x * (Φ (v x + k x) - Φ (v x) - deriv Φ (v x) * k x)) μ :=
    hψ.mul (((hΦ.continuous.comp_aestronglyMeasurable (hv.add hk)).sub
      (hΦ.continuous.comp_aestronglyMeasurable hv)).sub
        ((hL.continuous.comp_aestronglyMeasurable hv).mul hk))
  apply integrable_and_norm_integral_le_of_quadratic_bound k hr
  filter_upwards [hb] with x hx
  calc
    ‖ψ x * (Φ (v x + k x) - Φ (v x) - deriv Φ (v x) * k x)‖ =
        ‖ψ x‖ * ‖Φ (v x + k x) - Φ (v x) - deriv Φ (v x) * k x‖ := norm_mul _ _
    _ ≤ A * ((L : ℝ) * ‖k x‖ ^ 2) :=
      mul_le_mul hx (norm_scalar_remainder_le_of_lipschitz_deriv hΦ hL _ _)
        (norm_nonneg _) hA
    _ = (A * L) * (k x) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
      ring

end HeatKernel
