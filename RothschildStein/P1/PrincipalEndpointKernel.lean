-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalParameterAction
public import RothschildStein.Definitions.testMultiplierOn

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- An actual coordinate term in the endpoint
parameter derivative, with the local field coefficient absorbed into
the output test cutoff (BB Lemma 11.18, p. 549). -/
def PrincipalTerm.endpointCoordinateDerivative (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) (j : Fin N) :
    PrincipalTerm F :=
  { t.parameterDerivative (Pi.single j 1, 0) with
    a := (testMultiplierOn F.V (fun ξ => Y ξ j)
      ((contDiff_apply ℝ ℝ j).comp_contDiffOn hY) t.a) }

/-- The coordinate term has the exact scalar
endpoint derivative of the actual model kernel. -/
theorem PrincipalTerm.endpointCoordinateDerivative_kernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) (j : Fin N)
    (ξ η : Fin N → ℝ) :
    (t.endpointCoordinateDerivative Y hY j).kernel ξ η =
      t.a ξ * t.b η * (Y ξ j *
        fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
          t.modelKernel p.1 p.2 (F.Θ η ξ)) (ξ, η) (Pi.single j 1, 0)) := by
  change (t.a ξ * Y ξ j) * t.b η *
    (t.parameterDerivative (Pi.single j 1, 0)).modelKernel ξ η (F.Θ η ξ) = _
  rw [t.parameterDerivative_modelKernel]
  ring

/-- Each endpoint contribution retains type λ;
the endpoint field may be only locally smooth. -/
theorem PrincipalTerm.endpointCoordinateDerivative_isTypeKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) (j : Fin N)
    (lam : ℕ) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F lam (t.endpointCoordinateDerivative Y hY j).kernel :=
  (t.endpointCoordinateDerivative Y hY j).isTypeKernel lam hd

/-- The finite endpoint derivative kernel. -/
def PrincipalTerm.endpointKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (ξ η : Fin N → ℝ) : ℝ :=
  ∑ j, (t.endpointCoordinateDerivative Y hY j).kernel ξ η

/-- The full endpoint contribution retains type λ. -/
theorem PrincipalTerm.endpointKernel_isTypeKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (lam : ℕ) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F lam (t.endpointKernel Y hY) := by
  apply IsTypeKernel.sum
  intro j _
  exact t.endpointCoordinateDerivative_isTypeKernel Y hY j lam hd

/-- The constructed finite kernel is exactly
the derivative in the output endpoint direction, holding the model coordinate fixed. -/
theorem PrincipalTerm.endpointKernel_eq (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (ξ η : Fin N → ℝ) :
    t.endpointKernel Y hY ξ η = t.a ξ * t.b η *
      fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        t.modelKernel p.1 p.2 (F.Θ η ξ)) (ξ, η) (Y ξ, 0) := by
  classical
  have he : ((Y ξ, 0) : (Fin N → ℝ) × (Fin N → ℝ)) =
      ∑ j, Y ξ j • ((Pi.single j 1, 0) : (Fin N → ℝ) × (Fin N → ℝ)) := by
    simp only [Prod.smul_mk, smul_zero, ← prod_mk_sum, Finset.sum_const_zero]
    exact congrArg (fun z : Fin N → ℝ => (z, (0 : Fin N → ℝ))) (pi_eq_sum_univ' (Y ξ))
  simp only [endpointKernel, endpointCoordinateDerivative_kernel]
  rw [he, map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum]

end RothschildStein.P1
