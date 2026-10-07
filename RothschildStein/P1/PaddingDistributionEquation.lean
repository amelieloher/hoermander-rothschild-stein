-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDomainSmoothness
public import RothschildStein.P1.PaddingFiberTestOperator
public import RothschildStein.P1.PaddingDistributionTensorDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- The actual distribution identity (L + Δ_z)(T ⊗ 1) =
(LT) ⊗ 1 in compact-test pairings, for arbitrary distributions.
No function representative or global coefficient extension is assumed. -/
theorem paddingDistributionTensor_equation {q n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (T F : _root_.Distribution Ω B ⊤)
    (hEq : ∀ ψ : _root_.TestFunction Ω ℝ ⊤,
      T (sumSquaresWithDriftTransposeTest Ω X hX ψ) = F ψ)
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingDistributionTensorOneCLM Ω U hU T
      (sumSquaresWithDriftTransposeTest U (paddingVectorFields (d := d) X)
        (contDiffOn_paddingVectorFields_projection (Ω : Set (Fin n → ℝ))
          (U : Set (Fin (n + d) → ℝ)) hU X hX) φ) =
      paddingDistributionTensorOneCLM Ω U hU F φ := by
  rw [paddingDistributionTensorOneCLM_apply,
    paddingFiberTestCLM_sumSquaresWithDriftTranspose, paddingDistributionTensorOneCLM_apply]
  exact hEq (paddingFiberTestCLM Ω U hU φ)

end RothschildStein.P1
