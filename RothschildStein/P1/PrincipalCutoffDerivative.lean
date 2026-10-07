-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.S.ClassicalWords

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- The output-cutoff derivative is an actual
principal term of unchanged degree. Only local smoothness of the field
on V is required (BB Lemma 11.18, p. 549). -/
def PrincipalTerm.cutoffDerivative (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) : PrincipalTerm F :=
  { t with a := (S.wordDerivativeTest F.V (fun _ : Fin 1 => Y)
      (fun _ => hY) [0] t.a) }

/-- The cutoff term is precisely (Ya)bDΓ. -/
theorem PrincipalTerm.cutoffDerivative_kernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (ξ η : Fin N → ℝ) :
    (t.cutoffDerivative Y hY).kernel ξ η =
      fieldDerivative Y t.a ξ * t.b η * t.modelKernel ξ η (F.Θ η ξ) := rfl

/-- The output-cutoff contribution keeps type λ. -/
theorem PrincipalTerm.cutoffDerivative_isTypeKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (lam : ℕ) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F lam (t.cutoffDerivative Y hY).kernel :=
  (t.cutoffDerivative Y hY).isTypeKernel lam hd

end RothschildStein.P1
