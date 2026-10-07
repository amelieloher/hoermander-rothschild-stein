-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3

/-- Removing the radius weights costs an explicit polynomial in the radius. -/
theorem second_norm_sum_le_scaled_sum (r U H S : ℝ) (hr : 0 < r)
    (hU : 0 ≤ U) (hH : 0 ≤ H) (hS : 0 ≤ S) :
    U+H+S ≤ (1+r+r^2)*(S+r⁻¹*H+r⁻¹^2*U) := by
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hcancel : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hcancel2 : r^2*r⁻¹^2 = 1 := by nlinarith [sq_nonneg (r*r⁻¹-1)]
  have h1 : S ≤ S+r⁻¹*H+r⁻¹^2*U := by
    linarith [mul_nonneg hi.le hH, mul_nonneg (sq_nonneg r⁻¹) hU]
  have h2 : H ≤ r*(S+r⁻¹*H+r⁻¹^2*U) := by
    nlinarith [mul_nonneg hr.le hS, mul_nonneg hr.le (mul_nonneg (sq_nonneg r⁻¹) hU)]
  have h3 : U ≤ r^2*(S+r⁻¹*H+r⁻¹^2*U) := by
    nlinarith [mul_nonneg (sq_nonneg r) hS,
      mul_nonneg (sq_nonneg r) (mul_nonneg hi.le hH)]
  nlinarith

end RothschildStein.H3
