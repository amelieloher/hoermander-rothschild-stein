-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NonlinearEnergyDifferentiability
public import HeatKernel.Moser.TimeAverageDerivatives

/-! # Spatial integral chain rules along square integrable time curves

The Fréchet derivative of a weighted nonlinear energy gives its time derivative as the
spatial first-variation integral. In particular this applies to one-sided time averages.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- A differentiable L² curve has the spatial first-variation derivative for its weighted
nonlinear integral energy. -/
theorem hasDerivAt_weighted_nonlinear_energy {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {t : ℝ} (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => ∫ x, ψ x * Φ (u s x) ∂μ)
      (∫ x, ψ x * deriv Φ (u t x) * v x ∂μ) t := by
  obtain ⟨g, hg, hd⟩ := exists_hasFDerivAt_weighted_nonlinear_energy
    hΦ hL hzero hdzero hψ hA hb (u t)
  have he : (innerSL ℝ g) v = ∫ x, ψ x * deriv Φ (u t x) * v x ∂μ := by
    rw [innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    simp [hx, mul_comm]
  simpa only [Function.comp_def, he] using hd.comp_hasDerivAt t hu

/-- The forward averaged nonlinear energy has the spatial first-variation derivative
almost everywhere for a locally integrable L² curve. -/
theorem ae_hasDerivAt_nonlinear_energy_forwardTimeAverage {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} (hu : LocallyIntegrable u volume) (h : ℝ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun s => ∫ x, ψ x * Φ (forwardTimeAverage h u s x) ∂μ)
      (∫ x, ψ x * deriv Φ (forwardTimeAverage h u t x) *
        (h⁻¹ • (u (t + h) - u t)) x ∂μ) t := by
  filter_upwards [ae_hasDerivAt_forwardTimeAverage hu h] with t ht
  exact hasDerivAt_weighted_nonlinear_energy hΦ hL hzero hdzero hψ hA hb ht

/-- A differentiable time weight adds its product-rule term to the nonlinear averaged energy. -/
theorem ae_hasDerivAt_timeWeighted_nonlinear_energy_forwardTimeAverage {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} (hu : LocallyIntegrable u volume) (h : ℝ)
    {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun s => χ s * ∫ x, ψ x * Φ (forwardTimeAverage h u s x) ∂μ)
      (deriv χ t * (∫ x, ψ x * Φ (forwardTimeAverage h u t x) ∂μ) +
        χ t * ∫ x, ψ x * deriv Φ (forwardTimeAverage h u t x) *
          (h⁻¹ • (u (t + h) - u t)) x ∂μ) t := by
  filter_upwards [ae_hasDerivAt_nonlinear_energy_forwardTimeAverage
    hΦ hL hzero hdzero hψ hA hb hu h] with t ht
  exact (hχ t).hasDerivAt.mul ht

end HeatKernel
