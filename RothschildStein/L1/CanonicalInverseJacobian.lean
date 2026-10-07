-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalCommonDensityPackage
public import RothschildStein.Definitions.absoluteJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1.CanonicalFrameChartData

/-- The matrix definition of the absolute Jacobian equals the coordinate-free absolute
continuous-linear determinant on the same finite coordinate carrier. -/
theorem absoluteJacobian_eq_det {N : ℕ}
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (ξ : Fin N → ℝ) :
    absoluteJacobian f ξ = |(fderiv ℝ f ξ).det| := by
  unfold absoluteJacobian
  rw [LinearMap.det_toMatrix]

/-- The actual inverse coordinate Jacobian is the
reciprocal forward density, by differentiating the inverse identity. -/
theorem theta_jacobian_eq_inverse_density {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {η ξ : Fin N → ℝ}
    (hη : η ∈ ball x C.radius) (hξ : ξ ∈ ball x C.radius) :
    absoluteJacobian (fun z => C.theta (η,z)) ξ =
      (C.forwardDensity (η,C.theta (η,ξ)))⁻¹ := by
  let f := fun z => C.theta (η,z)
  let g := fun u => canonicalFrameMap C.time C.flow (η,u)
  have hf := (C.theta_right_contDiffAt η ξ hη hξ).differentiableAt (by simp)
  have hg := (C.forward_at_inverse_contDiffAt η ξ hη hξ).differentiableAt (by simp)
  have hd : (fderiv ℝ g (f ξ)).comp (fderiv ℝ f ξ) = ContinuousLinearMap.id ℝ (Fin N → ℝ) := by
    rw [← fderiv_comp ξ hg hf]
    exact (C.right_inverse_eventually η ξ hη hξ).fderiv_eq.trans fderiv_id
  have hdet : (fderiv ℝ g (f ξ)).toLinearMap.det *
      (fderiv ℝ f ξ).toLinearMap.det = 1 := by
    have he := congrArg ContinuousLinearMap.det hd
    change LinearMap.det ((fderiv ℝ g (f ξ)).toLinearMap.comp
      (fderiv ℝ f ξ).toLinearMap) = LinearMap.det LinearMap.id at he
    simpa only [LinearMap.det_comp, LinearMap.det_id] using he
  have habs : C.forwardDensity (η,C.theta (η,ξ)) * |(fderiv ℝ f ξ).det| = 1 := by
    simpa only [abs_mul, abs_one, forwardDensity, ContinuousLinearMap.det, f, g]
      using congrArg abs hdet
  rw [absoluteJacobian_eq_det]
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using habs)

end RothschildStein.L1.CanonicalFrameChartData
