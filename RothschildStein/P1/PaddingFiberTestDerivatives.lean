-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberIntegralDirections
public import RothschildStein.P1.PaddingFiberTestContinuity
public import Hormander.Interface.EuclideanDivergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

private theorem join_basis_base {n d : ℕ} (j : Fin n) :
    joinPoint (Hormander.Interface.basisVec j) (0 : Fin d → ℝ) =
      Hormander.Interface.basisVec (Fin.castAdd d j) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · simp [joinPoint, Hormander.Interface.basisVec, Pi.single_apply, Fin.ext_iff]
  · have h : Fin.natAdd n k ≠ Fin.castAdd d j := by
      intro he
      have hval := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    simp [joinPoint, Hormander.Interface.basisVec, h]

private theorem join_basis_fiber {n d : ℕ} (j : Fin d) :
    joinPoint (0 : Fin n → ℝ) (Hormander.Interface.basisVec j) =
      Hormander.Interface.basisVec (Fin.natAdd n j) := by
  funext i
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · have h : Fin.castAdd d k ≠ Fin.natAdd n j := by
      intro he
      have hval := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      omega
    simp [joinPoint, Hormander.Interface.basisVec, h]
  · simp [joinPoint, Hormander.Interface.basisVec, Pi.single_apply, Fin.ext_iff]

private theorem lineDerivTest_eq_fderiv {m : ℕ} (U : Opens (Fin m → ℝ))
    (φ : _root_.TestFunction U ℝ ⊤) (v x : Fin m → ℝ) :
    (_root_.TestFunction.lineDerivCLM ℝ v φ : _root_.TestFunction U ℝ ⊤) x =
      fderiv ℝ φ x v := by
  rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv

/-- Base-coordinate test derivatives commute with the
LF fiber-integration map on actual test functions. -/
theorem paddingFiberTestCLM_lineDeriv_base {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) (j : Fin n) :
    paddingFiberTestCLM Ω U hU
      (_root_.TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec (Fin.castAdd d j)) φ) =
    _root_.TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec j)
      (paddingFiberTestCLM Ω U hU φ) := by
  ext x
  rw [paddingFiberTestCLM_apply, lineDerivTest_eq_fderiv]
  have he : (paddingFiberTestCLM Ω U hU φ : (Fin n → ℝ) → ℝ) =
      fun y => ∫ z : Fin d → ℝ, φ (joinPoint y z) :=
    funext (paddingFiberTestCLM_apply Ω U hU φ)
  rw [he, fderiv_joinPoint_fiberIntegral_apply φ.contDiff φ.hasCompactSupport]
  simp_rw [lineDerivTest_eq_fderiv, join_basis_base]

/-- Added-coordinate test derivatives have zero fiber integral;
therefore the added Laplacian vanishes on tensors with the constant fiber. -/
theorem paddingFiberTestCLM_lineDeriv_fiber {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) (j : Fin d) :
    paddingFiberTestCLM Ω U hU
      (_root_.TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec (Fin.natAdd n j)) φ) = 0 := by
  ext x
  rw [paddingFiberTestCLM_apply]
  simp_rw [lineDerivTest_eq_fderiv, ← join_basis_fiber]
  exact integral_fderiv_joinPoint_vertical_eq_zero φ.contDiff φ.hasCompactSupport x
    (Hormander.Interface.basisVec j)

end RothschildStein.P1
