-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Small parabolic cylinders around interior points -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace HeatKernel

/-- A terminal time above the chosen point that remains below the ambient top. -/
def interiorCylinderTop (T t r : ℝ) : ℝ := min T (t + r ^ 2 / 4)

/-- A point below the ambient top lies in the inner half of its small cylinder. -/
theorem mem_inner_time_interiorCylinderTop {T t r : ℝ} (ht : t < T) (hr : 0 < r) :
    t ∈ Ioo (interiorCylinderTop T t r - r ^ 2 / 2) (interiorCylinderTop T t r) := by
  constructor
  · have h := min_le_right T (t + r ^ 2 / 4)
    change min T (t + r ^ 2 / 4) - r ^ 2 / 2 < t
    nlinarith [sq_pos_of_pos hr]
  · exact lt_min ht (by nlinarith [sq_pos_of_pos hr])

/-- A positive lower-time gap contains the entire small outer cylinder. -/
theorem outer_time_interiorCylinderTop_subset {a A T t r : ℝ}
    (ht : t ∈ Ioo A T) (hgap : r ^ 2 ≤ A - a) :
    Ioo (interiorCylinderTop T t r - r ^ 2) (interiorCylinderTop T t r) ⊆ Ioo a T := by
  have htop : t ≤ interiorCylinderTop T t r :=
    le_min ht.2.le (by nlinarith [sq_nonneg r])
  intro s hs
  exact ⟨by linarith [ht.1, hs.1], hs.2.trans_le (min_le_left _ _)⟩

/-- A ball about an interior point fits in the outer ball when its radius is
bounded by the gap between the two concentric ambient radii. -/
theorem ball_subset_outer_ball_of_radius_gap {α : Type*} [PseudoMetricSpace α]
    {x x₀ : α} {ρ R r : ℝ} (hx : x ∈ ball x₀ ρ) (hgap : r ≤ R - ρ) :
    ball x r ⊆ ball x₀ R := by
  intro y hy
  apply lt_of_le_of_lt (dist_triangle y x x₀)
  exact (add_lt_add hy hx).trans_le (by linarith)

/-- Positive spatial and lower-time gaps supply a positive radius fitting both. -/
theorem exists_positive_radius_for_cylinder_gaps {ρ R a A : ℝ}
    (hspace : ρ < R) (htime : a < A) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R - ρ ∧ r ^ 2 ≤ A - a := by
  let r := min (R - ρ) (Real.sqrt (A - a))
  have hr : 0 < r := lt_min (sub_pos.mpr hspace) (Real.sqrt_pos.mpr (sub_pos.mpr htime))
  refine ⟨r, hr, min_le_left _ _, ?_⟩
  calc
    r ^ 2 ≤ Real.sqrt (A - a) ^ 2 :=
      pow_le_pow_left₀ hr.le (min_le_right _ _) _
    _ = A - a := Real.sq_sqrt (sub_nonneg.mpr htime.le)

end HeatKernel
