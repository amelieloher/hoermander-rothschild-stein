-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NonlinearEnergyChainRule
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Endpoint identities for nonlinear averaged energies

The spatial first-variation chain rule integrates to the energy endpoint difference whenever
the scalar weighted energy is absolutely continuous on the time interval.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- Absolute continuity of the scalar energy integrates the nonlinear averaged chain rule.
This hypothesis records the endpoint regularity required by the fundamental theorem of calculus. -/
theorem integral_timeWeighted_nonlinear_energy_forwardTimeAverage_of_absolutelyContinuous
    {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} (hu : LocallyIntegrable u volume) (h : ℝ)
    {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval
      (fun s => χ s * ∫ x, ψ x * Φ (forwardTimeAverage h u s x) ∂μ) a b) :
    (∫ t in a..b, deriv χ t * (∫ x, ψ x * Φ (forwardTimeAverage h u t x) ∂μ) +
      χ t * ∫ x, ψ x * deriv Φ (forwardTimeAverage h u t x) *
        (h⁻¹ • (u (t + h) - u t)) x ∂μ) =
      χ b * (∫ x, ψ x * Φ (forwardTimeAverage h u b x) ∂μ) -
        χ a * (∫ x, ψ x * Φ (forwardTimeAverage h u a x) ∂μ) := by
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_hasDerivAt_timeWeighted_nonlinear_energy_forwardTimeAverage
    hΦ hL hzero hdzero hψ hA hb hu h hχ] with t ht
  intro _
  exact ht.deriv.symm

end HeatKernel
