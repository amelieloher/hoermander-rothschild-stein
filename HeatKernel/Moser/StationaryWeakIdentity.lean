-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Stationary weak identities

Compactly supported time derivatives integrate to zero. Fubini's theorem combines
this fact with a spatial weak identity to give its stationary space-time counterpart.
See Sturm 1996, Proposition 3.2.
-/

@[expose] public section

open MeasureTheory Set

namespace HeatKernel

/-- The derivative of a compactly supported continuously differentiable function has zero integral. -/
theorem integral_deriv_eq_zero_of_hasCompactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) : ∫ t, deriv f t = 0 := by
  have hi : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.integrableOn hi.integrableOn,
    HasCompactSupport.integral_Iic_deriv_eq hf hc,
    HasCompactSupport.integral_Ioi_deriv_eq hf hc]
  exact add_neg_cancel _

/-- A stationary multiplier annihilates the time derivative when the product is integrable. -/
theorem integral_stationary_mul_timeDeriv_eq_zero_of_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {u : α → ℝ} {φ : ℝ → α → ℝ}
    (hφ : ∀ x, ContDiff ℝ 1 (fun t => φ t x))
    (hc : ∀ x, HasCompactSupport (fun t => φ t x))
    (hi : Integrable (fun z : ℝ × α => u z.2 * deriv (fun t => φ t z.2) z.1)
      (volume.prod μ)) :
    (∫ z : ℝ × α, u z.2 * deriv (fun t => φ t z.2) z.1 ∂volume.prod μ) = 0 := by
  rw [integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  rw [integral_const_mul, integral_deriv_eq_zero_of_hasCompactSupport (hφ x) (hc x),
    mul_zero]
  rfl

end HeatKernel
