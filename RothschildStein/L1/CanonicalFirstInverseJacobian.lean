-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalInverseJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1.CanonicalFrameChartData

/-- Reversing the endpoints preserves the absolute coordinate Jacobian. -/
theorem theta_first_jacobian_eq_swapped {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {η ξ : Fin N → ℝ}
    (hη : η ∈ ball x C.radius) (hξ : ξ ∈ ball x C.radius) :
    absoluteJacobian (fun z => C.theta (z,ξ)) η =
      absoluteJacobian (fun z => C.theta (ξ,z)) η := by
  have he : (fun z => C.theta (z,ξ)) =ᶠ[𝓝 η]
      (fun z => -C.theta (ξ,z)) := by
    filter_upwards [isOpen_ball.mem_nhds hη] with z hz
    exact C.antisymmetric (ξ,z) (C.basePatch_subset ⟨hξ,hz⟩)
  rw [absoluteJacobian_eq_det, absoluteJacobian_eq_det, he.fderiv_eq,
    fderiv_fun_neg]
  exact abs_linear_det_neg (fderiv ℝ (fun z => C.theta (ξ,z)) η).toLinearMap

/-- The first-endpoint Jacobian
uses the density at the other endpoint and negated coordinates. -/
theorem theta_first_jacobian_eq_inverse_density {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {η ξ : Fin N → ℝ}
    (hη : η ∈ ball x C.radius) (hξ : ξ ∈ ball x C.radius)
    (hu : C.theta (η,ξ) ∈ ball 0 C.radius) :
    absoluteJacobian (fun z => C.theta (z,ξ)) η =
      (C.firstVariableDensity (ξ,C.theta (η,ξ)))⁻¹ := by
  rw [C.theta_first_jacobian_eq_swapped hη hξ,
    C.theta_jacobian_eq_inverse_density hξ hη,
    C.firstVariableDensity_eq _ ⟨hξ,hu⟩,
    C.antisymmetric (η,ξ) (C.basePatch_subset ⟨hη,hξ⟩)]

end RothschildStein.L1.CanonicalFrameChartData
