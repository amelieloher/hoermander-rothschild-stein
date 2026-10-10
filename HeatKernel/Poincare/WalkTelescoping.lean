-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! Telescoping real-valued differences along simple intersection chains. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace HeatKernel

/-- Summing endpoint-weighted edge estimates counts each interior vertex twice. -/
theorem abs_sub_le_two_mul_walk_sum_sub_endpoints {ι : Type*} (G : SimpleGraph ι)
    (c e : ι → ℝ) (hstep : ∀ i j, G.Adj i j → |c i - c j| ≤ e i + e j)
    {i j : ι} (p : G.Walk i j) :
    |c i - c j| ≤ 2 * (p.support.map e).sum - e i - e j := by
  induction p with
  | nil =>
      simp
      linarith
  | @cons i l j hil p ih =>
      have ht : |c i - c j| ≤ |c i - c l| + |c l - c j| := abs_sub_le _ _ _
      have he := hstep i l hil
      simp only [SimpleGraph.Walk.support_cons, List.map_cons, List.sum_cons]
      linarith

/-- Along a simple path, nonnegative vertex weights pay for at most two adjacent edges
at each vertex. -/
theorem abs_sub_le_two_mul_simple_path_sum {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι)
    (c e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hstep : ∀ i j, G.Adj i j → |c i - c j| ≤ e i + e j)
    {i j : ι} (p : G.Walk i j) (hp : p.IsPath) :
    |c i - c j| ≤ 2 * ∑ k ∈ p.support.toFinset, e k := by
  classical
  have ht := abs_sub_le_two_mul_walk_sum_sub_endpoints G c e hstep p
  rw [List.sum_toFinset e hp.support_nodup]
  linarith [he i, he j]

end HeatKernel
