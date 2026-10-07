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
the input test cutoff (BB Lemma 11.18, p. 549). -/
def PrincipalTerm.inputEndpointCoordinateDerivative (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) (j : Fin N) :
    PrincipalTerm F :=
  { t.parameterDerivative (0, Pi.single j 1) with
    b := (testMultiplierOn F.V (fun η => Y η j)
      ((contDiff_apply ℝ ℝ j).comp_contDiffOn hY) t.b) }

/-- The coordinate term has the exact scalar
endpoint derivative of the actual model kernel. -/
theorem PrincipalTerm.inputEndpointCoordinateDerivative_kernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) (j : Fin N)
    (ξ η : Fin N → ℝ) :
    (t.inputEndpointCoordinateDerivative Y hY j).kernel ξ η =
      t.a ξ * t.b η * (Y η j *
        fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
          t.modelKernel p.1 p.2 (F.Θ η ξ)) (ξ, η) (0, Pi.single j 1)) := by
  change t.a ξ * (t.b η * Y η j) *
    (t.parameterDerivative (0, Pi.single j 1)).modelKernel ξ η (F.Θ η ξ) = _
  rw [t.parameterDerivative_modelKernel]
  ring

/-- Each endpoint contribution retains type λ;
the endpoint field may be only locally smooth. -/
theorem PrincipalTerm.inputEndpointCoordinateDerivative_isTypeKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) (j : Fin N)
    (lam : ℕ) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F lam (t.inputEndpointCoordinateDerivative Y hY j).kernel :=
  (t.inputEndpointCoordinateDerivative Y hY j).isTypeKernel lam hd

/-- The finite endpoint derivative kernel. -/
def PrincipalTerm.inputEndpointKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (ξ η : Fin N → ℝ) : ℝ :=
  ∑ j, (t.inputEndpointCoordinateDerivative Y hY j).kernel ξ η

/-- The full endpoint contribution retains type λ. -/
theorem PrincipalTerm.inputEndpointKernel_isTypeKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (lam : ℕ) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F lam (t.inputEndpointKernel Y hY) := by
  apply IsTypeKernel.sum
  intro j _
  exact t.inputEndpointCoordinateDerivative_isTypeKernel Y hY j lam hd

/-- The constructed finite kernel is exactly
the derivative in the input endpoint direction, holding the model coordinate fixed. -/
theorem PrincipalTerm.inputEndpointKernel_eq (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ)))
    (ξ η : Fin N → ℝ) :
    t.inputEndpointKernel Y hY ξ η = t.a ξ * t.b η *
      fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        t.modelKernel p.1 p.2 (F.Θ η ξ)) (ξ, η) (0, Y η) := by
  classical
  have he : ((0, Y η) : (Fin N → ℝ) × (Fin N → ℝ)) =
      ∑ j, Y η j • ((0, Pi.single j 1) : (Fin N → ℝ) × (Fin N → ℝ)) := by
    simp only [Prod.smul_mk, smul_zero, ← prod_mk_sum, Finset.sum_const_zero]
    exact congrArg (fun z : Fin N → ℝ => ((0 : Fin N → ℝ), z)) (pi_eq_sum_univ' (Y η))
  simp only [inputEndpointKernel, inputEndpointCoordinateDerivative_kernel]
  rw [he, map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum]

end RothschildStein.P1
