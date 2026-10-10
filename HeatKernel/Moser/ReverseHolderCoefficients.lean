-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! Uniform coefficients for bottom-sharing small-positive-power iteration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace HeatKernel

/-- In the half-endpoint range, a cost of order `1 / p` is controlled by the
reverse-Hölder exponent difference with a factor independent of `p`. -/
theorem reverse_holder_cost_le_exponent_difference {p p₀ K : ℝ}
    (hp : 0 < p) (hp₀ : 0 < p₀) (hhalf : p ≤ p₀ / 2) (hK : 0 ≤ K) :
    K / p ≤ 2 * (1 / p - 1 / p₀) * K := by
  have h : 2 / p₀ ≤ 1 / p := (div_le_div_iff₀ hp₀ hp).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right h hK
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith

end HeatKernel
