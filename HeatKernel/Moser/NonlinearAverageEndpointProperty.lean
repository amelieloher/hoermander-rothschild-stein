-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeightedBoundedEnergyEndpoints

/-! # Weighted nonlinear endpoint identities along L² curves -/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- Every normalized nonlinearity with Lipschitz derivative, bounded spatial weight, and
smooth temporal weight satisfies the endpoint identity along the forward averages. -/
def HasWeightedNonlinearAverageEndpoints {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℝ → Lp ℝ 2 μ) : Prop :=
  ∀ (Φ : ℝ → ℝ) (L : ℝ≥0), Differentiable ℝ Φ → LipschitzWith L (deriv Φ) →
    Φ 0 = 0 → deriv Φ 0 = 0 →
    ∀ (ψ : α → ℝ) (A : ℝ≥0), AEStronglyMeasurable ψ μ →
      (∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 1 χ → ∀ h : ℝ, 0 < h → ∀ a b : ℝ,
        (∫ t in a..b, deriv χ t * (∫ x, ψ x * Φ (forwardTimeAverage h u t x) ∂μ) +
          χ t * ∫ x, ψ x * deriv Φ (forwardTimeAverage h u t x) *
            (h⁻¹ • (u (t + h) - u t)) x ∂μ) =
          χ b * (∫ x, ψ x * Φ (forwardTimeAverage h u b x) ∂μ) -
            χ a * (∫ x, ψ x * Φ (forwardTimeAverage h u a x) ∂μ)

/-- Essential boundedness and local square integrability give all weighted nonlinear
average endpoint identities. -/
theorem hasWeightedNonlinearAverageEndpoints_of_bounded_memLp {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {u : ℝ → Lp ℝ 2 μ}
    (hu : MemLp u 2 volume) {M : ℝ≥0} (hb : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) :
    HasWeightedNonlinearAverageEndpoints u := by
  intro Φ L hΦ hL hzero hdzero ψ A hψ hψA χ hχ h hh a b
  exact integral_timeWeighted_nonlinear_energy_forwardTimeAverage_eq_sub
    hΦ hL hzero hdzero hψ hψA (hu.locallyIntegrable (by norm_num)) hb hh hχ a b

end HeatKernel
