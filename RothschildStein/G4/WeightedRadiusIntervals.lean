-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

namespace RothschildStein.G4

/-- Positive-radius weighted comparisons are equivalent to a
single signed power inequality (BB p. 454). -/
theorem weighted_radius_comparison_iff {A B r : ℝ} {U V : ℤ} (hr : 0 < r) :
    A * r ^ U ≤ B * r ^ V ↔ A * r ^ (U - V) ≤ B := by
  rw [zpow_sub₀ hr.ne', ← mul_div_assoc, div_le_iff₀ (zpow_pos hr V)]

/-- Every positive-radius weighted comparison cuts out an
interval, including negative weight deficits (BB p. 454). -/
theorem ordConnected_weighted_radius_comparison {A B : ℝ} (hA : 0 ≤ A) (U V : ℤ) :
    OrdConnected {r : ℝ | 0 < r ∧ A * r ^ U ≤ B * r ^ V} := by
  constructor
  intro x hx y hy r hr
  have hrpos : 0 < r := hx.1.trans_le hr.1
  refine ⟨hrpos, (weighted_radius_comparison_iff hrpos).mpr ?_⟩
  by_cases hUV : 0 ≤ U - V
  · have hp : r ^ (U - V) ≤ y ^ (U - V) := zpow_le_zpow_left₀ hUV hrpos.le hr.2
    exact (mul_le_mul_of_nonneg_left hp hA).trans
      ((weighted_radius_comparison_iff hy.1).mp hy.2)
  · have hneg : 0 ≤ -(U - V) := by omega
    have hp₀ : x ^ (-(U - V)) ≤ r ^ (-(U - V)) :=
      zpow_le_zpow_left₀ hneg hx.1.le hr.1
    have hi := (inv_le_inv₀ (zpow_pos hrpos (-(U - V)))
      (zpow_pos hx.1 (-(U - V)))).mpr hp₀
    have hp : r ^ (U - V) ≤ x ^ (U - V) := by
      simpa only [← zpow_neg, neg_neg] using hi
    exact (mul_le_mul_of_nonneg_left hp hA).trans
      ((weighted_radius_comparison_iff hx.1).mp hx.2)

end RothschildStein.G4
