-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalJacobianNonzero
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

/-- The actual coefficient chart inverse identity holds as a neighborhood
identity at every point of the common coefficient patch. -/
theorem forward_inverse_eventually (C : CanonicalFrameChartData Ω Y x)
    (η u : Fin N → ℝ) (hη : η ∈ ball x C.radius) (hu : u ∈ ball 0 C.radius) :
    (fun v => C.theta (η,canonicalFrameMap C.time C.flow (η,v))) =ᶠ[𝓝 u] id := by
  filter_upwards [isOpen_ball.mem_nhds hu] with v hv
  exact (C.coefficients (η,v) ⟨hη,hv⟩).2.2

/-- The forward canonical coefficient Jacobian has strictly positive
absolute value throughout the common coefficient patch. -/
theorem forward_abs_jacobian_pos (C : CanonicalFrameChartData Ω Y x)
    (η u : Fin N → ℝ) (hη : η ∈ ball x C.radius) (hu : u ∈ ball 0 C.radius) :
    0 < |(fderiv ℝ (fun v => canonicalFrameMap C.time C.flow (η,v)) u).det| := by
  have hf : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun v => canonicalFrameMap C.time C.flow (η,v)) u :=
    (C.forward_smooth.contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hη,hu⟩)).comp u
      (contDiffAt_const.prodMk contDiffAt_id)
  apply abs_pos.mpr
  exact coordinateJacobian_ne_zero_of_right_inverse
    (fun v => canonicalFrameMap C.time C.flow (η,v)) (fun ξ => C.theta (η,ξ)) u
    (hf.differentiableAt (by simp))
    ((C.theta_right_contDiffAt_of_mem η (canonicalFrameMap C.time C.flow (η,u))
      (C.coefficients (η,u) ⟨hη,hu⟩).2.1).differentiableAt (by simp))
    (C.forward_inverse_eventually η u hη hu)
end CanonicalFrameChartData
end RothschildStein.L1
