-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartIdentities
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The spatial patch can shrink while the coefficient radius
stays fixed. Thus all pair coordinates lie in any prescribed smaller
coefficient ball, even when the inverse frame has a large norm. -/
theorem exists_small_base_patch (D : CanonicalFrameChartData Ω Y x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ D.radius ∧
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r, D.theta (η,ξ) ∈ ball 0 δ := by
  have hx : x ∈ ball x D.radius := mem_ball_self D.radius_pos
  have hc : ContinuousAt D.theta (x,x) := (D.theta_smooth.contDiffAt (D.inverseDomain_open.mem_nhds
    (D.basePatch_subset ⟨hx,hx⟩))).continuousAt
  have hm : {q | D.theta q ∈ ball 0 δ} ∈ 𝓝 (x,x) :=
    hc.preimage_mem_nhds (by
      rw [D.theta_diagonal x hx]
      exact isOpen_ball.mem_nhds (mem_ball_self hδ))
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hm
  let r := min ε D.radius
  have hr : 0 < r := lt_min hε D.radius_pos
  refine ⟨r,hr,min_le_right _ _,?_⟩
  intro η hη ξ hξ
  apply hsub
  rw [mem_ball,Prod.dist_eq,max_lt_iff]
  exact ⟨ball_subset_ball (min_le_left _ _) hη,ball_subset_ball (min_le_left _ _) hξ⟩
end CanonicalFrameChartData
end RothschildStein.L1
