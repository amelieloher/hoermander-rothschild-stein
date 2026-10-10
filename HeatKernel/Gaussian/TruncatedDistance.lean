-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! # Bounded distance weights for endpoint estimates

Truncating distance at the separation of two centers gives a bounded
one-Lipschitz weight with the required bounds on their endpoint balls.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Metric
namespace HeatKernel.Gaussian

/-- Truncating distance at the separation of two centers preserves its
one-Lipschitz bound. -/
theorem lipschitzWith_truncated_distance {X : Type*} [PseudoMetricSpace X] (x y : X) :
    LipschitzWith 1 (fun z ↦ min (dist x z) (dist x y)) :=
  (LipschitzWith.dist_right x).min_const _

/-- The truncated distance lies between zero and the center separation. -/
theorem truncated_distance_bounds {X : Type*} [PseudoMetricSpace X] (x y z : X) :
    0 ≤ min (dist x z) (dist x y) ∧ min (dist x z) (dist x y) ≤ dist x y :=
  ⟨le_min dist_nonneg dist_nonneg, min_le_right _ _⟩

/-- The distance weight is bounded above by the radius on the first ball. -/
theorem truncated_distance_le_of_mem_ball {X : Type*} [PseudoMetricSpace X]
    {x y z : X} {r : ℝ} (hz : z ∈ ball x r) :
    min (dist x z) (dist x y) ≤ r := by
  have H : dist x z < r := by simpa [dist_comm] using hz
  exact (min_le_left _ _).trans H.le

/-- On the second ball, the weight is at least separation minus radius. -/
theorem sub_radius_le_truncated_distance_of_mem_ball {X : Type*} [PseudoMetricSpace X]
    {x y z : X} {r : ℝ} (hr : 0 ≤ r) (hz : z ∈ ball y r) :
    dist x y - r ≤ min (dist x z) (dist x y) := by
  apply le_min
  · have H : dist z y < r := hz
    have T := dist_triangle x z y
    linarith
  · linarith

/-- Multiplying the second-ball bound by a nonnegative weight parameter gives
the logarithmic lower bound used in local weighted energy. -/
theorem weighted_sub_radius_le_truncated_distance {X : Type*} [PseudoMetricSpace X]
    {x y z : X} {r β : ℝ} (hr : 0 ≤ r) (hβ : 0 ≤ β) (hz : z ∈ ball y r) :
    2 * β * (dist x y - r) ≤ 2 * β * min (dist x z) (dist x y) :=
  mul_le_mul_of_nonneg_left (sub_radius_le_truncated_distance_of_mem_ball hr hz)
    (mul_nonneg (by norm_num) hβ)

end HeatKernel.Gaussian
