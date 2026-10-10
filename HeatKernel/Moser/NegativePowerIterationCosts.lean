-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Uniform accumulation of logarithmic costs in negative-power iteration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open Filter Finset
open scoped Topology BigOperators
namespace HeatKernel

/-- Geometrically weighted affine iteration costs have an explicit sum, with all
exponent dependence contained in the final factor `1 / p`. -/
theorem hasSum_negative_power_iteration_cost {q A B p : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => (A + B * j) * q ^ j / p)
      ((A / (1 - q) + B * q / (1 - q) ^ 2) / p) := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h := (((hasSum_geometric_of_lt_one hq hq1).mul_left A).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left B)).div_const p
  convert h using 1
  · funext j
    ring
  · ring

/-- Every finite negative-power iteration has the same exponent-independent
majorant for its accumulated logarithmic cost. -/
theorem sum_negative_power_iteration_cost_le {q A B p : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 < p) (n : ℕ) :
    (∑ j ∈ range n, (A + B * j) * q ^ j / p) ≤
      (A / (1 - q) + B * q / (1 - q) ^ 2) / p := by
  have hs := hasSum_negative_power_iteration_cost (A := A) (B := B) (p := p) hq hq1
  exact (hs.summable.sum_le_tsum (range n) (fun j _ => by positivity)).trans_eq hs.tsum_eq

end HeatKernel
