-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BoundedNonlinearEnergyEndpoints

/-! # Time-weighted endpoint identities for bounded nonlinear energies

A continuously differentiable time weight is absolutely continuous on each compact interval.
Multiplying by the averaged nonlinear energy preserves this regularity and yields the
weighted endpoint identity without a separate hypothesis on the weighted energy.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- A smooth time weight preserves absolute continuity of a bounded averaged nonlinear energy. -/
theorem absolutelyContinuousOnInterval_timeWeighted_nonlinear_energy_forwardTimeAverage
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ≥0} (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} (hu : LocallyIntegrable u volume)
    {M : ℝ≥0} (huM : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) {h : ℝ} (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => χ t * ∫ x, ψ x * Φ (forwardTimeAverage h u t x) ∂μ) a b := by
  have henergy := absolutelyContinuousOnInterval_nonlinear_energy_forwardTimeAverage
    hΦ hL hzero hdzero hψ hb hu huM hh a b
  simpa only [Pi.mul_def] using hχ.contDiffOn.absolutelyContinuousOnInterval.mul henergy

/-- A bounded L² curve and a smooth time weight satisfy the weighted nonlinear endpoint identity. -/
theorem integral_timeWeighted_nonlinear_energy_forwardTimeAverage_eq_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ≥0} (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} (hu : LocallyIntegrable u volume)
    {M : ℝ≥0} (huM : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) {h : ℝ} (hh : 0 < h)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (a b : ℝ) :
    (∫ t in a..b, deriv χ t * (∫ x, ψ x * Φ (forwardTimeAverage h u t x) ∂μ) +
      χ t * ∫ x, ψ x * deriv Φ (forwardTimeAverage h u t x) *
        (h⁻¹ • (u (t + h) - u t)) x ∂μ) =
      χ b * (∫ x, ψ x * Φ (forwardTimeAverage h u b x) ∂μ) -
        χ a * (∫ x, ψ x * Φ (forwardTimeAverage h u a x) ∂μ) := by
  exact integral_timeWeighted_nonlinear_energy_forwardTimeAverage_of_absolutelyContinuous
    hΦ hL hzero hdzero hψ A.coe_nonneg hb hu h (hχ.differentiable (by norm_num))
    (absolutelyContinuousOnInterval_timeWeighted_nonlinear_energy_forwardTimeAverage
      hΦ hL hzero hdzero hψ hb hu huM hh hχ a b)

end HeatKernel
