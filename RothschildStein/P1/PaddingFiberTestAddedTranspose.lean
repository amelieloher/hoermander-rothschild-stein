-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberTestDerivatives
public import RothschildStein.P1.PaddingFieldSmoothness
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1

private theorem fieldTransposeTest_constant {m : ℕ}
    (U : Opens (Fin m → ℝ)) (v : Fin m → ℝ) (φ : _root_.TestFunction U ℝ ⊤) :
    fieldTransposeTest U (fun _ => v) contDiffOn_const φ =
      -_root_.TestFunction.lineDerivCLM ℝ v φ := by
  ext ξ
  change fieldTransposeTest U (fun _ => v) contDiffOn_const φ ξ =
    -((_root_.TestFunction.lineDerivCLM ℝ v φ : _root_.TestFunction U ℝ ⊤) ξ)
  rw [S.fieldTransposeTest_apply, S.fieldTranspose_formula _ _ _ (differentiableAt_const v)
    (φ.contDiff.differentiable (by simp) ξ)]
  rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp),
    (φ.contDiff.differentiable (by simp) ξ).lineDeriv_eq_fderiv]
  simp [fieldDerivative, Hormander.Interface.euclideanDivergence]

/-- The transpose of every added diffusion has zero fiber
integral on actual compact tests. -/
theorem paddingFiberTestCLM_fieldTranspose_added {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (j : Fin d) (φ : _root_.TestFunction U ℝ ⊤) :
    paddingFiberTestCLM Ω U hU
      (fieldTransposeTest U (paddingDiffusionField (n := n) j)
        (contDiff_paddingDiffusionField j).contDiffOn φ) = 0 := by
  have he : fieldTransposeTest U (paddingDiffusionField (n := n) j)
      (contDiff_paddingDiffusionField j).contDiffOn φ =
      -_root_.TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec (Fin.natAdd n j)) φ :=
    fieldTransposeTest_constant U (Hormander.Interface.basisVec (Fin.natAdd n j)) φ
  rw [he, map_neg, paddingFiberTestCLM_lineDeriv_fiber, neg_zero]

end RothschildStein.P1
