-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BoundedTimeAverages
public import HeatKernel.Moser.NonlinearEnergyLipschitz
public import HeatKernel.Moser.NonlinearEnergyEndpoints

/-! # Absolute continuity and endpoint identities for bounded averaged energies

Essentially bounded L² curves have Lipschitz time averages with bounded image. Local
Lipschitz bounds for the nonlinear energy then supply the scalar absolute continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace HeatKernel

/-- The nonlinear energy of the forward average of an essentially bounded L² curve is
absolutely continuous on every compact time interval. -/
theorem absolutelyContinuousOnInterval_nonlinear_energy_forwardTimeAverage {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ≥0} (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    {u : ℝ → Lp ℝ 2 μ} (hu : LocallyIntegrable u volume)
    {M : ℝ≥0} (huM : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) {h : ℝ} (hh : 0 < h) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t => ∫ x, ψ x * Φ (forwardTimeAverage h u t x) ∂μ) a b := by
  have hLip := lipschitzWith_forwardTimeAverage_of_ae_norm_le hu huM h
  have hmaps : MapsTo (forwardTimeAverage h u) (uIcc a b)
      (Metric.closedBall 0 (M : ℝ)) := by
    intro t _
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_forwardTimeAverage_le_of_ae_norm_le huM hh t
  have henergy := lipschitzOnWith_weighted_nonlinear_energy_closedBall hΦ hL hzero hdzero hψ hb M
  simpa only [Function.comp_def] using henergy.comp_absolutelyContinuousOnInterval hmaps
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval

end HeatKernel
