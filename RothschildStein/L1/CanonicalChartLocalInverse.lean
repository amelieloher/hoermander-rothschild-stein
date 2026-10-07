-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartData
public import RothschildStein.L1.RightInverseLocalChart
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

/-- Joint smoothness restricts to every second-variable chart germ. -/
theorem theta_right_contDiffAt_of_mem (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => D.theta (η,z)) ξ :=
  (D.theta_smooth.contDiffAt (D.inverseDomain_open.mem_nhds hq)).comp ξ
    (contDiffAt_const.prodMk contDiffAt_id)

/-- The forward map is smooth at every actual inverse parameter. -/
theorem forward_at_inverse_contDiffAt_of_mem (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u => canonicalFrameMap D.time D.flow (η,u)) (D.theta (η,ξ)) := by
  have ht : D.time ∈ Ioo (-D.timeRadius) D.timeRadius :=
    ⟨by linarith [D.time_pos,D.timeRadius_pos],D.time_lt⟩
  have hp : (η,D.theta (η,ξ)) ∈ canonicalFrameDomain D.time (ball (0,x) D.initialRadius) :=
    D.inverse_parameters (η,ξ) hq
  exact ((canonicalFrameMap_contDiffOn D.time ht D.flow D.flow_smooth).contDiffAt
    ((canonicalFrameDomain_isOpen D.time isOpen_ball).mem_nhds hp)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)

/-- The actual right inverse identity as a germ at every spatial point
of the chosen patch. -/
theorem right_inverse_eventually (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hξ : ξ ∈ ball x D.radius) :
    (fun z => canonicalFrameMap D.time D.flow (η,D.theta (η,z))) =ᶠ[𝓝 ξ] id := by
  filter_upwards [isOpen_ball.mem_nhds hξ] with z hz
  exact D.right_inverse (η,z) (D.basePatch_subset ⟨hη,hz⟩)

/-- Joint chart smoothness restricts to each second-variable chart. -/
theorem theta_right_contDiffAt (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hξ : ξ ∈ ball x D.radius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => D.theta (η,z)) ξ :=
  (D.theta_smooth.contDiffAt (D.inverseDomain_open.mem_nhds
    (D.basePatch_subset ⟨hη,hξ⟩))).comp ξ (contDiffAt_const.prodMk contDiffAt_id)

/-- Actual inverse parameters belong to the forward flow domain, so
the forward map is smooth at their value. -/
theorem forward_at_inverse_contDiffAt (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hξ : ξ ∈ ball x D.radius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u => canonicalFrameMap D.time D.flow (η,u)) (D.theta (η,ξ)) := by
  have ht : D.time ∈ Ioo (-D.timeRadius) D.timeRadius :=
    ⟨by linarith [D.time_pos,D.timeRadius_pos],D.time_lt⟩
  have hp : (η,D.theta (η,ξ)) ∈ canonicalFrameDomain D.time (ball (0,x) D.initialRadius) :=
    D.inverse_parameters (η,ξ) (D.basePatch_subset ⟨hη,hξ⟩)
  exact ((canonicalFrameMap_contDiffOn D.time ht D.flow D.flow_smooth).contDiffAt
    ((canonicalFrameDomain_isOpen D.time isOpen_ball).mem_nhds hp)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)

end CanonicalFrameChartData
end RothschildStein.L1
