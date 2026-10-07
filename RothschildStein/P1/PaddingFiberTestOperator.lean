-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDomainSmoothness
public import RothschildStein.P1.PaddingFiberTestTranspose
public import RothschildStein.P1.PaddingFiberTestAddedTranspose
public import RothschildStein.Definitions.sumSquaresWithDriftTransposeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1

private theorem field_transpose_eq_of_field_eq {N : ℕ}
    (U : Opens (Fin N → ℝ)) (V W : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (U : Set (Fin N → ℝ)))
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W (U : Set (Fin N → ℝ)))
    (he : V = W) (ψ : _root_.TestFunction U ℝ ⊤) :
    fieldTransposeTest U V hV ψ = fieldTransposeTest U W hW ψ := by
  subst W
  rfl

private theorem padding_transpose_with_smoothness {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hp : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (paddingVectorFields (d := d) X i)
      (U : Set (Fin (n + d) → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingFiberTestCLM Ω U hU
      (sumSquaresWithDriftTransposeTest U (paddingVectorFields (d := d) X)
        hp φ) =
      sumSquaresWithDriftTransposeTest Ω X hX (paddingFiberTestCLM Ω U hU φ) := by
  have hb (i : Fin (q + d + 1)) (j : Fin (q + 1))
      (he : paddingVectorFields X i = paddingBaseField (d := d) (X j))
      (ψ : _root_.TestFunction U ℝ ⊤) :
      paddingFiberTestCLM Ω U hU (fieldTransposeTest U (paddingVectorFields X i) (hp i) ψ) =
        fieldTransposeTest Ω (X j) (hX j) (paddingFiberTestCLM Ω U hU ψ) := by
    rw [field_transpose_eq_of_field_eq U _ _ (hp i)
      ((contDiffOn_paddingBaseField (Ω : Set (Fin n → ℝ)) (X j) (hX j)).mono hU) he]
    exact paddingFiberTestCLM_fieldTranspose_base Ω U hU (X j) (hX j) ψ
  have ha (j : Fin d) (ψ : _root_.TestFunction U ℝ ⊤) :
      paddingFiberTestCLM Ω U hU
        (fieldTransposeTest U (paddingVectorFields X (Fin.natAdd q j).succ)
          (hp (Fin.natAdd q j).succ) ψ) = 0 := by
    rw [field_transpose_eq_of_field_eq U _ _ _
      (contDiff_paddingDiffusionField j).contDiffOn (paddingVectorFields_added X j)]
    exact paddingFiberTestCLM_fieldTranspose_added Ω U hU j ψ
  unfold sumSquaresWithDriftTransposeTest
  rw [map_add, map_sum, Fin.sum_univ_add, hb 0 0 (paddingVectorFields_zero X)]
  congr 1
  have hz : (∑ j : Fin d, paddingFiberTestCLM Ω U hU
      (fieldTransposeTest U (paddingVectorFields X (Fin.natAdd q j).succ)
        (hp (Fin.natAdd q j).succ)
        (fieldTransposeTest U (paddingVectorFields X (Fin.natAdd q j).succ)
          (hp (Fin.natAdd q j).succ) φ))) = 0 := by
    simp only [ha, Finset.sum_const_zero]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb _ i.succ (paddingVectorFields_original X i),
    hb _ i.succ (paddingVectorFields_original X i)]


/-- The complete padded transpose commutes with actual LF
fiber integration. The added diffusion squares vanish, while every
original diffusion and the original drift is preserved. -/
theorem paddingFiberTestCLM_sumSquaresWithDriftTranspose {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingFiberTestCLM Ω U hU
      (sumSquaresWithDriftTransposeTest U (paddingVectorFields (d := d) X)
        (contDiffOn_paddingVectorFields_projection (Ω : Set (Fin n → ℝ))
          (U : Set (Fin (n + d) → ℝ)) hU X hX) φ) =
      sumSquaresWithDriftTransposeTest Ω X hX (paddingFiberTestCLM Ω U hU φ) := by
  exact padding_transpose_with_smoothness Ω U hU X hX
    (contDiffOn_paddingVectorFields_projection (Ω : Set (Fin n → ℝ))
      (U : Set (Fin (n + d) → ℝ)) hU X hX) φ

end RothschildStein.P1
