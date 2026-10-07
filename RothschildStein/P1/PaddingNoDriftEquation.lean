-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftOperator
public import RothschildStein.P1.PaddingDistributionTensorDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- The no-drift padded distribution equation for
arbitrary real-test distributions, with real or complex values. -/
theorem paddingDistributionTensor_noDrift_equation {q n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (T F : Distribution Ω B (⊤ : ℕ∞))
    (hEq : ∀ ψ : _root_.TestFunction Ω ℝ ⊤, T (sumSquaresTransposeTest Ω X hX ψ) = F ψ)
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingDistributionTensorOneCLM Ω U hU T
      (sumSquaresTransposeTest U (paddingNoDriftVectorFields (d := d) X)
        (contDiffOn_paddingNoDriftVectorFields_projection (Ω : Set (Fin n → ℝ))
          (U : Set (Fin (n + d) → ℝ)) hU X hX) φ) =
      paddingDistributionTensorOneCLM Ω U hU F φ := by
  rw [paddingDistributionTensorOneCLM_apply, paddingFiberTestCLM_sumSquaresTranspose,
    paddingDistributionTensorOneCLM_apply]
  exact hEq (paddingFiberTestCLM Ω U hU φ)

end RothschildStein.P1
