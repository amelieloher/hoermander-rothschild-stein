-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalRadialFlow
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Actual vector fields pulled into a coordinate chart. -/
def coordinatePullbackField {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (θ K : (Fin N → ℝ) → (Fin N → ℝ)) (i : Fin N) (u : Fin N → ℝ) : Fin N → ℝ :=
  fderiv ℝ θ (K u) (Y i (K u))

/-- The inverse chain rule converts the actual radial flow
identity into the Euler field identity in canonical coordinates. -/
theorem coordinatePullbackField_radial_identity {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (θ K : (Fin N → ℝ) → (Fin N → ℝ)) (u : Fin N → ℝ)
    (hθ : DifferentiableAt ℝ θ (K u))
    (hcurve : HasDerivAt (fun s : ℝ => K (s • u)) (frameCoefficientField Y (u,K u)) 1)
    (hinv : (fun s : ℝ => θ (K (s • u))) =ᶠ[𝓝 1] (fun s => s • u)) :
    ∑ i, u i • coordinatePullbackField Y θ K i u = u := by
  have hθ1 : HasFDerivAt θ (fderiv ℝ θ (K u)) (K ((1 : ℝ) • u)) := by
    simpa only [one_smul] using hθ.hasFDerivAt
  have hd := hθ1.comp_hasDerivAt 1 hcurve
  have hd' := hd.congr_of_eventuallyEq hinv.symm
  have he := hd'.unique ((hasDerivAt_id (1 : ℝ)).smul_const u)
  simpa only [one_smul,coordinatePullbackField,frameCoefficientField,map_sum,map_smul] using he
end RothschildStein.L1
