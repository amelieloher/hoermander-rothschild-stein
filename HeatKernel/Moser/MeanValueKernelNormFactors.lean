-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-! # Comparison of Jacobian and ball-volume normalizations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped ENNReal
namespace HeatKernel

/-- The inverse parabolic Jacobian is bounded by the endpoint volume normalization
with a constant depending only on the unit ball volume. -/
theorem identity_kernel_endpoint_prefactor_le (Q : ℕ) (C : ℝ) {r b : ℝ}
    (hr : 0 < r) (hb : 0 < b) :
    C ^ 2 * ((2 * r) ^ (Q + 2))⁻¹ ≤
      (C * (b + 1)) ^ 2 / (r ^ 2 * ((2 * r) ^ Q * b)) := by
  apply (le_div_iff₀ (show 0 < r ^ 2 * ((2 * r) ^ Q * b) by positivity)).mpr
  have heq : C ^ 2 * ((2 * r) ^ (Q + 2))⁻¹ *
      (r ^ 2 * ((2 * r) ^ Q * b)) = C ^ 2 * (b / 4) := by
    rw [pow_add]
    field_simp
    ring
  rw [heq, mul_pow]
  apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
  nlinarith [sq_nonneg b]

/-- Every positive-power norm has the endpoint normalization, with a factor
independent of the radius and determined by the exponent and unit ball volume. -/
theorem identity_kernel_endpoint_positive_power_norm_factor_le (Q : ℕ) {p r b : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hb : 0 < b) :
    ENNReal.ofReal (((2 * r) ^ (Q + 2))⁻¹) ^ (1 / p) ≤
      ENNReal.ofReal ((b + 1) ^ (2 / p)) *
        ((ENNReal.ofReal (r ^ 2 * ((2 * r) ^ Q * b)))⁻¹) ^ (1 / p) := by
  have hD : 0 < r ^ 2 * ((2 * r) ^ Q * b) := by positivity
  have hB : 0 ≤ b + 1 := by linarith
  have hreal := identity_kernel_endpoint_prefactor_le Q 1 hr hb
  norm_num only [one_pow, one_mul] at hreal
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_div_of_pos hD, ENNReal.ofReal_pow hB, div_eq_mul_inv] at h
  calc
    _ ≤ ((ENNReal.ofReal (b + 1)) ^ 2 *
      (ENNReal.ofReal (r ^ 2 * ((2 * r) ^ Q * b)))⁻¹) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_two,
        ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / p) = 2 / p by ring,
        ENNReal.ofReal_rpow_of_pos (by linarith : 0 < b + 1)]

end HeatKernel
