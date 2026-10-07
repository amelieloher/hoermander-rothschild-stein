-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalRadialIdentity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Inverse canonical coordinates take the actual tangent frame
to the standard coordinate basis at zero (BB (10.16), p. 501). -/
theorem coordinatePullbackField_basis_values {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (θ K : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hK0 : K 0 = x) (hθ : DifferentiableAt ℝ θ x)
    (hK : HasFDerivAt K (frameValueCLM Y x) 0)
    (hinv : (fun u => θ (K u)) =ᶠ[𝓝 0] (id : (Fin N → ℝ) → (Fin N → ℝ)))
    (i : Fin N) :
    coordinatePullbackField Y θ K i 0 = Pi.single i (1 : ℝ) := by
  have hθK : DifferentiableAt ℝ θ (K 0) := by rwa [hK0]
  have hc := hθK.hasFDerivAt.comp 0 hK
  have he := (hc.congr_of_eventuallyEq hinv.symm).unique (hasFDerivAt_id (0 : Fin N → ℝ))
  have hh := congrArg (fun A : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) => A (Pi.single i 1)) he
  have hb : frameValueCLM Y x (Pi.single i 1) = Y i x := by
    classical
    simp [frameValueCLM_apply,frameCoefficientField,Pi.single_apply]
  change fderiv ℝ θ (K 0) (frameValueCLM Y x (Pi.single i 1)) = Pi.single i 1 at hh
  simpa only [coordinatePullbackField,hK0,hb] using hh
end RothschildStein.L1
