-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartLocalInverse
public import Mathlib.LinearAlgebra.Determinant
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1

/-- A square smooth right inverse has a nonzero actual coordinate Jacobian. -/
theorem coordinateJacobian_ne_zero_of_right_inverse {N : ℕ}
    (θ K : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hθ : DifferentiableAt ℝ θ x) (hK : DifferentiableAt ℝ K (θ x))
    (hright : (K ∘ θ) =ᶠ[𝓝 x] (id : (Fin N → ℝ) → (Fin N → ℝ))) :
    (fderiv ℝ θ x).det ≠ 0 := by
  have hi := coordinateDerivative_injective_of_right_inverse θ K x hθ hK hright
  intro hz
  have hk := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  exact hk (LinearMap.ker_eq_bot.mpr hi)

namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

end CanonicalFrameChartData
end RothschildStein.L1
