-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import RothschildStein.G2.Algebra
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension
import Mathlib.Tactic

/-! # Reduction of homogeneous kernels to unit time

Parabolic dilation covariance identifies each positive-time kernel value with a
unit-time value. The inverse dilation and time power are computed explicitly.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel.Gaussian

/-- Parabolic covariance reduces positive-time kernel values to unit time for
an abstract dilation action with inverse dilations. -/
theorem kernel_eq_unit_time_of_covariance {α : Type*} (p : ℝ → α → α → ℝ)
    (δ : ℝ → α → α) (Q : ℝ)
    (hinv : ∀ r, 0 < r → ∀ x, δ r (δ r⁻¹ x) = x)
    (hcov : ∀ r, 0 < r → ∀ s, 0 < s → ∀ x y,
      p (r ^ 2 * s) (δ r x) (δ r y) = r ^ (-Q) * p s x y)
    {t : ℝ} (ht : 0 < t) (x y : α) :
    p t x y = t ^ (-Q / 2) * p 1 (δ (t ^ (-(1 : ℝ) / 2)) x) (δ (t ^ (-(1 : ℝ) / 2)) y) := by
  have hr := Real.sqrt_pos.mpr ht
  have h := hcov (Real.sqrt t) hr 1 zero_lt_one
    (δ (Real.sqrt t)⁻¹ x) (δ (Real.sqrt t)⁻¹ y)
  rw [mul_one, Real.sq_sqrt ht.le, hinv _ hr, hinv _ hr] at h
  have hi : t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [neg_div, Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  have he : (Real.sqrt t) ^ (-Q) = t ^ (-Q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  simpa only [hi, he] using h

/-- Homogeneous-group kernel covariance gives the exact unit-time scaling
formula in the original coordinates. -/
theorem homogeneous_kernel_eq_unit_time_of_covariance {N : ℕ}
    (G : RothschildStein.HomogeneousGroup N) (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hcov : ∀ r, 0 < r → ∀ s, 0 < s → ∀ x y,
      p (r ^ 2 * s) (G.dilate r x) (G.dilate r y) =
        r ^ (-(G.homogeneousDimension : ℝ)) * p s x y)
    {t : ℝ} (ht : 0 < t) (x y : Fin N → ℝ) :
    p t x y = t ^ (-(G.homogeneousDimension : ℝ) / 2) *
      p 1 (G.dilate (t ^ (-(1 : ℝ) / 2)) x) (G.dilate (t ^ (-(1 : ℝ) / 2)) y) := by
  apply kernel_eq_unit_time_of_covariance p G.dilate _ ?_ hcov ht x y
  intro r hr z
  rw [RothschildStein.G2.dilate_dilate, mul_inv_cancel₀ hr.ne', RothschildStein.G2.dilate_one]

end HeatKernel.Gaussian
