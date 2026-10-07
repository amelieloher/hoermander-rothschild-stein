-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalForwardJacobianSmooth
public import RothschildStein.L1.CompactPositiveFactorBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The positive origin normalization has uniform positive lower and
upper bounds on the smaller closed base patch. -/
theorem forward_origin_density_compact_bounds (C : CanonicalFrameChartData Ω Y x) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ η ∈ closedBall x (C.radius/2),
      lo ≤ |(fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (η,u)) 0).det| ∧
      |(fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (η,u)) 0).det| ≤ hi := by
  have h0 : (0 : Fin N → ℝ) ∈ ball 0 C.radius := mem_ball_self C.radius_pos
  have hc := C.forward_abs_jacobian_contDiffOn.comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun η hη => ⟨hη,h0⟩)
  have hsub : closedBall x (C.radius/2) ⊆ ball x C.radius :=
    closedBall_subset_ball (by linarith [C.radius_pos])
  exact compact_positive_factor_bounds (isCompact_closedBall x (C.radius/2))
    ⟨x,mem_closedBall_self (by linarith [C.radius_pos])⟩ _
    (hc.continuousOn.mono hsub) (fun η hη => C.forward_abs_jacobian_pos η 0 (hsub hη) h0)
end CanonicalFrameChartData
end RothschildStein.L1
