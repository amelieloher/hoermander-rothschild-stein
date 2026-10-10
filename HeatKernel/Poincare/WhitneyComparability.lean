-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyRadius
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.FieldSimp

/-! Radius comparison and containment for intersecting dilates of boundary-distance balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- Boundary-distance balls whose c-fold dilates meet have radii within a factor two
when the boundary separation constant exceeds 3c. -/
theorem boundaryBall_radii_comparable_of_dilates_intersect {E : Type*} [PseudoMetricSpace E]
    (U : Set E) {x z : E} {κ c : ℝ} (hc : 0 ≤ c) (hκ : 3 * c < κ)
    (hmeet : (ball x (c * (infDist x Uᶜ / κ)) ∩
      ball z (c * (infDist z Uᶜ / κ))).Nonempty) :
    infDist x Uᶜ / κ ≤ 2 * (infDist z Uᶜ / κ) ∧
      infDist z Uᶜ / κ ≤ 2 * (infDist x Uᶜ / κ) := by
  have hk : 0 < κ := by linarith
  have hrad : ∀ w : E, infDist w Uᶜ = κ * (infDist w Uᶜ / κ) := by
    intro w
    field_simp [hk.ne']
  obtain ⟨y, hyx, hyz⟩ := hmeet
  have hd : dist x z ≤ c * (infDist x Uᶜ / κ + infDist z Uᶜ / κ) := by
    have ht := dist_triangle x y z
    have hx := mem_ball.mp hyx
    have hz := mem_ball.mp hyz
    rw [dist_comm y x] at hx
    nlinarith
  refine ⟨radius_le_two_mul_of_boundaryDistance (lipschitz_infDist_pt Uᶜ)
    (div_nonneg infDist_nonneg hk.le) hc hκ (hrad x) (hrad z) hd, ?_⟩
  apply radius_le_two_mul_of_boundaryDistance (lipschitz_infDist_pt Uᶜ)
    (div_nonneg infDist_nonneg hk.le) hc hκ (hrad z) (hrad x)
  simpa only [dist_comm, add_comm] using hd

/-- A ball in a family of comparable radii whose c-fold dilates contain the same point
lies in one ball of radius (2c+2) times the reference radius. -/
theorem ball_subset_of_common_dilate_point {E : Type*} [PseudoMetricSpace E]
    {x y : E} {a a₀ c : ℝ} (hc : 0 ≤ c) (ha : a ≤ 2 * a₀)
    (hy : y ∈ ball x (c * a)) : ball x a ⊆ ball y ((2 * c + 2) * a₀) := by
  intro w hw
  have hwx := mem_ball.mp hw
  have hxy := mem_ball.mp hy
  rw [dist_comm y x] at hxy
  apply mem_ball.mpr
  calc
    dist w y ≤ dist w x + dist x y := dist_triangle w x y
    _ < a + c * a := add_lt_add hwx hxy
    _ = (1 + c) * a := by ring
    _ ≤ (1 + c) * (2 * a₀) := mul_le_mul_of_nonneg_left ha (by linarith)
    _ = (2 * c + 2) * a₀ := by ring

end HeatKernel
