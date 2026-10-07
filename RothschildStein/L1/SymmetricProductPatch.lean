-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Metric
namespace RothschildStein.L1

/-- A diagonal point in an open joint domain has a symmetric,
relatively compact product patch inside that domain. -/
theorem exists_symmetric_product_patch {N : ℕ}
    {W : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hW : IsOpen W)
    (x : Fin N → ℝ) (hx : (x,x) ∈ W) :
    ∃ r : ℝ, 0 < r ∧ ball x r ×ˢ ball x r ⊆ W ∧ IsCompact (closedBall x r) := by
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hW (x,x) hx
  refine ⟨r,hr,?_,isCompact_closedBall x r⟩
  intro q hq
  apply hsub
  rw [mem_ball,Prod.dist_eq,max_lt_iff]
  exact ⟨hq.1,hq.2⟩
end RothschildStein.L1
