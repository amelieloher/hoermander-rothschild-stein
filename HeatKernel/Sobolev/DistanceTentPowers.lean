-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

/-! # Measurability, boundedness and support of distance tent powers -/

@[expose] public section
open Set Metric
namespace HeatKernel.Sobolev

/-- Positive natural powers of a distance tent are measurable, nonnegative,
bounded by one, and supported in the corresponding open ball. -/
theorem distance_tent_pow_properties {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (x : E) {r : ℝ} (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) :
    Measurable (fun y => max (1 - dist x y / r) 0 ^ n) ∧
    (∀ y, 0 ≤ max (1 - dist x y / r) 0 ^ n) ∧
    (∀ y, ‖max (1 - dist x y / r) 0 ^ n‖ ≤ 1) ∧
    Function.support (fun y => max (1 - dist x y / r) 0 ^ n) ⊆ ball x r := by
  refine ⟨by fun_prop, fun y => pow_nonneg (le_max_right _ _) _, ?_, ?_⟩
  · intro y
    have hzero : 0 ≤ max (1 - dist x y / r) 0 := le_max_right _ _
    have hone : max (1 - dist x y / r) 0 ≤ 1 :=
      max_le (by have := div_nonneg (dist_nonneg : 0 ≤ dist x y) hr.le; linarith) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hzero n)]
    exact pow_le_one₀ hzero hone
  · intro y hy
    by_contra hnot
    have hd : r ≤ dist x y := by simpa only [mem_ball, not_lt, dist_comm y x] using hnot
    have hdiv : 1 ≤ dist x y / r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hd)
    have hz : max (1 - dist x y / r) 0 = 0 := max_eq_right (by linarith)
    exact hy (by simp [hz, Nat.ne_of_gt hn])

end HeatKernel.Sobolev
