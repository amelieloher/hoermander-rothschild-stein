-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.KernelScaling
import Mathlib.Tactic

/-! # Kernel scaling with the natural homogeneous dimension

The inverse natural power appearing in parabolic covariance equals the negative
real power used in Gaussian estimates. The exact unit-time reduction therefore
applies directly to that covariance convention.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel.Gaussian

/-- The natural-power convention for parabolic covariance gives the exact
homogeneous unit-time kernel formula. -/
theorem homogeneous_kernel_eq_unit_time_of_nat_covariance {N : ℕ}
    (G : RothschildStein.HomogeneousGroup N) (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hcov : ∀ t r, 0 < t → 0 < r → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y)
    {t : ℝ} (ht : 0 < t) (x y : Fin N → ℝ) :
    p t x y = t ^ (-(G.homogeneousDimension : ℝ) / 2) *
      p 1 (G.dilate (t ^ (-(1 : ℝ) / 2)) x) (G.dilate (t ^ (-(1 : ℝ) / 2)) y) := by
  apply homogeneous_kernel_eq_unit_time_of_covariance G p ?_ ht x y
  intro r hr s hs a b
  rw [hcov s r hs hr, Real.rpow_neg hr.le, Real.rpow_natCast]

end HeatKernel.Gaussian
