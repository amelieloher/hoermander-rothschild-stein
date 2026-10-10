-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueIteration
import Mathlib.Tactic

/-! # Explicit constants in geometric mean-value iteration -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
namespace HeatKernel

/-- Summing the logarithmic iteration costs gives an explicit finite constant. -/
theorem tsum_geometric_iteration_cost {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) :
    (∑' j : ℕ, (a + b * (j : ℝ)) * ρ ^ j) =
      a * (1 - ρ)⁻¹ + b * (ρ / (1 - ρ) ^ 2) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using hρone
  have h₀ := (summable_geometric_of_norm_lt_one hn).mul_left a
  have h₁ := (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable.mul_left b
  simp_rw [add_mul, mul_assoc]
  rw [h₀.tsum_add h₁, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_norm_lt_one hn, tsum_coe_mul_geometric_of_norm_lt_one hn]

/-- Positive-power iteration has a uniform bound with an explicit exponential constant. -/
theorem le_exp_explicit_cost_mul_of_iteration {Y : ℕ → ℝ} {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hY : 0 ≤ Y 0)
    (hstep : ∀ j, Y (j + 1) ≤ Real.exp ((a + b * (j : ℝ)) * ρ ^ j) * Y j)
    (n : ℕ) :
    Y n ≤ Real.exp (a * (1 - ρ)⁻¹ + b * (ρ / (1 - ρ) ^ 2)) * Y 0 := by
  simpa only [tsum_geometric_iteration_cost hρ hρone] using
    le_exp_geometric_cost_mul_of_iteration hρ hρone ha hb hY hstep n

end HeatKernel
