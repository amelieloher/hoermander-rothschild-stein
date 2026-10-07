-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalWordRemainder
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1
open G3

/-- The corrected inverse sign: model inversion
of Theta(eta,xi) is Theta(xi,eta), and both equal minus Theta(eta,xi). -/
theorem canonicalTheta_inverse_identity {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    {Ω : Set (Fin (freeDimension a s p) → ℝ)} {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η ξ : Fin (freeDimension a s p) → ℝ) (hq : (η,ξ) ∈ C.inverseDomain) :
    D.group.inv (C.theta (η,ξ)) = C.theta (ξ,η) ∧ C.theta (ξ,η) = -C.theta (η,ξ) := by
  have ha := C.antisymmetric (η,ξ) hq
  exact ⟨(freeModel_inv D _).trans ha.symm, ha⟩
end RothschildStein.L1
