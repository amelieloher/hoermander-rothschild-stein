-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftSmoothness
public import RothschildStein.P1.PaddingFiberTestOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

private theorem drift_transpose_eq_of_family_eq {q n : ℕ}
    (U : Opens (Fin n → ℝ))
    (V W : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) (U : Set (Fin n → ℝ)))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) (U : Set (Fin n → ℝ)))
    (he : V = W) (ψ : _root_.TestFunction U ℝ ⊤) :
    sumSquaresWithDriftTransposeTest U V hV ψ =
      sumSquaresWithDriftTransposeTest U W hW ψ := by
  subst W
  rfl

/-- No-drift diffusion padding commutes with actual LF fiber
integration for the sum-of-squares transpose. The proof
reuses the drift identity through a temporary zero-drift equation adapter. -/
theorem paddingFiberTestCLM_sumSquaresTranspose {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingFiberTestCLM Ω U hU
      (sumSquaresTransposeTest U (paddingNoDriftVectorFields (d := d) X)
        (contDiffOn_paddingNoDriftVectorFields_projection (Ω : Set (Fin n → ℝ))
          (U : Set (Fin (n + d) → ℝ)) hU X hX) φ) =
      sumSquaresTransposeTest Ω X hX (paddingFiberTestCLM Ω U hU φ) := by
  let hN := contDiffOn_paddingNoDriftVectorFields_projection (Ω : Set (Fin n → ℝ))
    (U : Set (Fin (n + d) → ℝ)) hU X hX
  let hP := contDiffOn_paddingVectorFields_projection (Ω : Set (Fin n → ℝ))
    (U : Set (Fin (n + d) → ℝ)) hU (P2.zeroDrift X) (P2.zeroDrift_contDiffOn hX)
  have hop : sumSquaresWithDriftTransposeTest U
      (paddingVectorFields (d := d) (P2.zeroDrift X)) hP φ =
      sumSquaresTransposeTest U (paddingNoDriftVectorFields (d := d) X) hN φ :=
    (drift_transpose_eq_of_family_eq U _ _ hP (P2.zeroDrift_contDiffOn hN)
      (paddingVectorFields_zeroDrift_eq X) φ).trans
        (P2.sumSquaresWithDriftTransposeTest_zeroDrift U _ hN φ)
  have hd := paddingFiberTestCLM_sumSquaresWithDriftTranspose
    Ω U hU (P2.zeroDrift X) (P2.zeroDrift_contDiffOn hX) φ
  rw [hop, P2.sumSquaresWithDriftTransposeTest_zeroDrift] at hd
  exact hd

end RothschildStein.P1
