-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.P1.PaddingCoordinates
public import RothschildStein.Definitions.fieldDerivative
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The actual one-variable lift with vertical coefficients depending
only on the base point (BB Proposition 10.17, (10.6)). -/
def oneVariableLift {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (u : Fin a → (Fin n → ℝ) → ℝ) :
    Fin a → (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) :=
  fun i ξ => joinPoint (X i (P1.paddingBaseCLM n 1 ξ))
    (fun _ : Fin 1 => u i (P1.paddingBaseCLM n 1 ξ))

/-- Projecting a lifted generator gives its original generator. -/
theorem oneVariableLift_base {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (u : Fin a → (Fin n → ℝ) → ℝ) (i : Fin a) (ξ : Fin (n+1) → ℝ) :
    P1.paddingBaseCLM n 1 (oneVariableLift X u i ξ) =
      X i (P1.paddingBaseCLM n 1 ξ) :=
  P1.paddingBaseCLM_join n 1 _ _

/-- The chain rule for a base-dependent test function is independent
of the vertical coefficient (BB (10.6)). -/
theorem oneVariableLift_fieldDerivative_pullback {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (u : Fin a → (Fin n → ℝ) → ℝ) (i : Fin a)
    (f : (Fin n → ℝ) → ℝ) (ξ : Fin (n+1) → ℝ)
    (hf : DifferentiableAt ℝ f (P1.paddingBaseCLM n 1 ξ)) :
    fieldDerivative (oneVariableLift X u i) (f ∘ P1.paddingBaseCLM n 1) ξ =
      fieldDerivative (X i) f (P1.paddingBaseCLM n 1 ξ) := by
  unfold fieldDerivative
  rw [fderiv_comp ξ hf (P1.paddingBaseCLM n 1).differentiableAt,
    (P1.paddingBaseCLM n 1).fderiv,ContinuousLinearMap.comp_apply,
    oneVariableLift_base]

/-- Differentiating the added coordinate gives the specified
vertical coefficient, with no dependence on the added coordinate. -/
theorem oneVariableLift_fieldDerivative_vertical {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (u : Fin a → (Fin n → ℝ) → ℝ) (i : Fin a) (ξ : Fin (n+1) → ℝ) :
    fieldDerivative (oneVariableLift X u i)
      (fun η => P1.paddingFiberCLM n 1 η 0) ξ =
      u i (P1.paddingBaseCLM n 1 ξ) := by
  let t : (Fin (n+1) → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (0 : Fin 1)).comp (P1.paddingFiberCLM n 1)
  change fderiv ℝ t ξ (oneVariableLift X u i ξ) = _
  rw [t.fderiv]
  change P1.paddingFiberCLM n 1 (oneVariableLift X u i ξ) 0 = _
  rw [oneVariableLift,P1.paddingFiberCLM_join]
end RothschildStein.L1
