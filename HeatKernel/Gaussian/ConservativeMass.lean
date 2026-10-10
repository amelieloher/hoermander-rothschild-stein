-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.KernelIntegrals
import Mathlib.Tactic

/-! # Real and nonnegative conservation identities

For nonnegative functions, unit real mass and unit nonnegative mass agree.
A nonzero real integral already ensures integrability of its integrand.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel.Gaussian

/-- A real function whose integral is one is integrable. -/
theorem integrable_of_integral_eq_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hmass : ∫ x, f x ∂μ = 1) : Integrable f μ := by
  apply Integrable.of_integral_ne_zero
  rw [hmass]
  exact one_ne_zero

/-- Nonnegative unit real mass gives unit nonnegative extended-real mass. -/
theorem lintegral_ofReal_eq_one_of_nonnegative_integral_eq_one {X : Type*}
    [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) (hn : ∀ x, 0 ≤ f x)
    (hmass : ∫ x, f x ∂μ = 1) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one μ f hmass)
    (Filter.Eventually.of_forall hn), hmass]
  norm_num

end HeatKernel.Gaussian
