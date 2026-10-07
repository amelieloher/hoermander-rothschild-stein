-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberTestDerivatives
public import RothschildStein.P1.PaddingFiberTestMultipliers
public import RothschildStein.P1.PaddingFieldSmoothness
public import RothschildStein.Definitions.fieldTransposeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1

private theorem paddingBaseField_component {n d : ℕ}
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (ξ : Fin (n + d) → ℝ) (j : Fin n) :
    paddingBaseField X ξ (Fin.castAdd d j) = X (basePoint ξ) j := by
  simp [paddingBaseField, joinPoint, paddingBaseCLM_apply]

/-- Fiber integration commutes with the field
transpose for every original field extended independently of the added
coordinates, with coefficients smooth only on the original domain. -/
theorem paddingFiberTestCLM_fieldTranspose_base {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingFiberTestCLM Ω U hU
      (fieldTransposeTest U (paddingBaseField (d := d) X)
        ((contDiffOn_paddingBaseField (Ω : Set (Fin n → ℝ)) X hX).mono hU) φ) =
    fieldTransposeTest Ω X hX (paddingFiberTestCLM Ω U hU φ) := by
  unfold fieldTransposeTest
  rw [map_neg, map_sum, Fin.sum_univ_add]
  simp_rw [paddingFiberTestCLM_lineDeriv_fiber]
  simp only [Finset.sum_const_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [paddingFiberTestCLM_lineDeriv_base]
  congr 1
  let a : (Fin n → ℝ) → ℝ := fun x => X x j
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)) :=
    (contDiff_apply ℝ ℝ j).comp_contDiffOn hX
  have hm : testMultiplierOn U (fun ξ => paddingBaseField X ξ (Fin.castAdd d j))
      ((contDiff_apply ℝ ℝ (Fin.castAdd d j)).comp_contDiffOn
        ((contDiffOn_paddingBaseField (Ω : Set (Fin n → ℝ)) X hX).mono hU)) φ =
      testMultiplierOn U (fun ξ => a (basePoint ξ))
        (contDiffOn_paddingBaseCoefficient Ω U hU a ha) φ := by
    ext ξ
    change φ ξ * paddingBaseField X ξ (Fin.castAdd d j) = φ ξ * a (basePoint ξ)
    rw [paddingBaseField_component]
  rw [hm, paddingFiberTestCLM_multiplier_base]

end RothschildStein.P1
