-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Convergent products in positive-power mean-value iteration -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators
namespace HeatKernel

/-- Successive multiplicative energy steps have an explicit finite product bound. -/
theorem le_exp_sum_mul_of_iteration {Y b : ℕ → ℝ}
    (hstep : ∀ j, Y (j + 1) ≤ Real.exp (b j) * Y j) (n : ℕ) :
    Y n ≤ Real.exp (∑ j ∈ range n, b j) * Y 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      Y (n + 1) ≤ Real.exp (b n) * Y n := hstep n
      _ ≤ Real.exp (b n) * (Real.exp (∑ j ∈ range n, b j) * Y 0) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (∑ j ∈ range (n + 1), b j) * Y 0 := by
        rw [sum_range_succ, Real.exp_add]
        ring

/-- A summable nonnegative logarithmic cost gives one bound for every iteration exponent. -/
theorem le_exp_tsum_mul_of_iteration {Y b : ℕ → ℝ}
    (hY : 0 ≤ Y 0) (hb : ∀ j, 0 ≤ b j) (hs : Summable b)
    (hstep : ∀ j, Y (j + 1) ≤ Real.exp (b j) * Y j) (n : ℕ) :
    Y n ≤ Real.exp (∑' j, b j) * Y 0 := by
  apply (le_exp_sum_mul_of_iteration hstep n).trans
  apply mul_le_mul_of_nonneg_right _ hY
  exact Real.exp_le_exp.mpr (hs.sum_le_tsum (range n) (fun j _ => hb j))

/-- The logarithmic cost of geometric exponent growth is summable. -/
theorem summable_geometric_iteration_cost {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) :
    Summable (fun j : ℕ => (a + b * (j : ℝ)) * ρ ^ j) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using hρone
  have h₀ := (summable_geometric_of_norm_lt_one hn).mul_left a
  have h₁ := (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable.mul_left b
  simpa only [add_mul, mul_assoc] using h₀.add h₁

/-- Linear logarithmic cutoff losses remain bounded under geometric exponent growth. -/
theorem le_exp_geometric_cost_mul_of_iteration {Y : ℕ → ℝ} {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hY : 0 ≤ Y 0)
    (hstep : ∀ j, Y (j + 1) ≤ Real.exp ((a + b * (j : ℝ)) * ρ ^ j) * Y j)
    (n : ℕ) :
    Y n ≤ Real.exp (∑' j : ℕ, (a + b * (j : ℝ)) * ρ ^ j) * Y 0 := by
  apply le_exp_tsum_mul_of_iteration hY _
    (summable_geometric_iteration_cost hρ hρone) hstep n
  intro j
  positivity

end HeatKernel
