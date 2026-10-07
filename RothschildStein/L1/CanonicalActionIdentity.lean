-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointPullbackFields
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual pullback field has the required
operator action, with the inverse substitution justified by the actual chart. -/
theorem pullbackField_action (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ)
    (hf : DifferentiableAt ℝ f (D.theta (η,ξ))) :
    fieldDerivative V (fun z => f (D.theta (η,z))) ξ =
      fieldDerivative (D.pullbackField η V) f (D.theta (η,ξ)) := by
  have hθ := (D.theta_right_contDiffAt_of_mem η ξ hq).differentiableAt (by simp)
  unfold fieldDerivative
  change fderiv ℝ (f ∘ fun z => D.theta (η,z)) ξ (V ξ) = _
  rw [fderiv_comp ξ hf hθ]
  unfold pullbackField
  rw [D.right_inverse (η,ξ) hq]
  rfl
end CanonicalFrameChartData
end RothschildStein.L1
