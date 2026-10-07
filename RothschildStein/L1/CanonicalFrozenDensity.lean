-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalFirstInverseJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1.CanonicalFrameChartData

/-- The common density package gives both exact reciprocal
Jacobians and the positivity of their normalized denominators
(BB Proposition 10.33, pp. 512–513). -/
theorem frozen_density_jacobians {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x)
    (c : (Fin N → ℝ) → ℝ)
    (wp wm : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ)
    (hc : ∀ η ∈ ball x C.radius, 0 < c η)
    (hfactor : ∀ q ∈ ball x C.radius ×ˢ ball 0 C.radius,
      C.forwardDensity q = c q.1 * (1 + wp q) ∧
      C.firstVariableDensity q = c q.1 * (1 + wm q))
    {η ξ : Fin N → ℝ} (hη : η ∈ ball x C.radius)
    (hξ : ξ ∈ ball x C.radius) (hu : C.theta (η,ξ) ∈ ball 0 C.radius) :
    0 < 1 + wp (η,C.theta (η,ξ)) ∧
    0 < 1 + wm (ξ,C.theta (η,ξ)) ∧
    absoluteJacobian (fun z => C.theta (η,z)) ξ =
      (c η * (1 + wp (η,C.theta (η,ξ))))⁻¹ ∧
    absoluteJacobian (fun z => C.theta (z,ξ)) η =
      (c ξ * (1 + wm (ξ,C.theta (η,ξ))))⁻¹ := by
  have hp := C.forward_abs_jacobian_pos η (C.theta (η,ξ)) hη hu
  change 0 < C.forwardDensity (η,C.theta (η,ξ)) at hp
  rw [(hfactor _ ⟨hη,hu⟩).1] at hp
  have hnu : -C.theta (η,ξ) ∈ ball 0 C.radius := by
    simpa only [mem_ball_zero_iff, norm_neg] using hu
  have hm := C.forward_abs_jacobian_pos ξ (-C.theta (η,ξ)) hξ hnu
  change 0 < C.forwardDensity (ξ,-C.theta (η,ξ)) at hm
  rw [← C.firstVariableDensity_eq (ξ,C.theta (η,ξ)) ⟨hξ,hu⟩,
    (hfactor _ ⟨hξ,hu⟩).2] at hm
  refine ⟨(mul_pos_iff_of_pos_left (hc η hη)).mp hp,
    (mul_pos_iff_of_pos_left (hc ξ hξ)).mp hm, ?_, ?_⟩
  · rw [C.theta_jacobian_eq_inverse_density hη hξ, (hfactor _ ⟨hη,hu⟩).1]
  · rw [C.theta_first_jacobian_eq_inverse_density hη hξ hu,
      (hfactor _ ⟨hξ,hu⟩).2]

end RothschildStein.L1.CanonicalFrameChartData
