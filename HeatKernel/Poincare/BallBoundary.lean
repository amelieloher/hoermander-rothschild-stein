-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneySelection

/-! Boundary-distance bounds and countable Whitney covers of metric balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open TopologicalSpace Set Metric

namespace HeatKernel

/-- A point on the radius-r sphere gives boundary distance at most two radii for every
point of the open ball. -/
theorem infDist_ball_compl_le_two_mul {E : Type*} [PseudoMetricSpace E]
    {x z w : E} {r : ℝ} (hz : z ∈ ball x r) (hw : dist x w = r) :
    infDist z (ball x r)ᶜ ≤ 2 * r := by
  have hwm : w ∈ (ball x r)ᶜ := by
    change ¬ dist w x < r
    rw [dist_comm, hw]
    exact lt_irrefl r
  calc
    infDist z (ball x r)ᶜ ≤ dist z w := infDist_le_dist_of_mem hwm
    _ ≤ dist z x + dist x w := dist_triangle z x w
    _ ≤ 2 * r := by rw [hw]; have hh := mem_ball.mp hz; linarith

/-- A sphere point makes the bounded-radius hypothesis of Whitney selection explicit
and yields the countable disjoint cover of the ball. -/
theorem exists_countable_disjoint_boundaryBall_cover_of_sphere_point {E : Type*}
    [MetricSpace E] [SeparableSpace E] (x w : E) {r κ : ℝ}
    (hw : dist x w = r) (hκ : 80 < κ) :
    ∃ C : Set E, C ⊆ ball x r ∧ C.Countable ∧
      (C.PairwiseDisjoint fun z => ball z (infDist z (ball x r)ᶜ / κ)) ∧
      ball x r = ⋃ z ∈ C, ball z (5 * (infDist z (ball x r)ᶜ / κ)) ∧
      ∀ z ∈ C, ball z (80 * (infDist z (ball x r)ᶜ / κ)) ⊆ ball x r := by
  refine exists_countable_disjoint_boundaryBall_cover isOpen_ball ?_ hκ
    (R := 2 * r / κ) ?_
  · refine ⟨w, ?_⟩
    change ¬ dist w x < r
    rw [dist_comm, hw]
    exact lt_irrefl r
  · intro z hz
    exact div_le_div_of_nonneg_right (infDist_ball_compl_le_two_mul hz hw) (by linarith)

end HeatKernel
