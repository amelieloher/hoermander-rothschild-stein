-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import RothschildStein.G1.DeterminantDerivative
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Sum of column replacements by `A M` equals trace times determinant, including singular matrices (BB Lemma 9.37, pp. 428–430). -/
theorem sum_det_updateCol_mul {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ j, (M.updateCol j (fun k => (A * M) k j)).det) = A.trace * M.det := by
  have heq : (∑ j, (M.updateCol j (fun k => (A * M) k j)).det) =
      (M.adjugate * (A * M)).trace := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    rfl
  rw [heq, Matrix.trace_mul_cycle', ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, mul_comm]

/-- Differentiate the column determinant along any vector field
(BB (9.29), p. 429). -/
theorem fieldDerivative_frameDet {ι : Type*} {n : ℕ}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} (B : Fin n → ι)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hZ : ∀ j, DifferentiableAt ℝ (Z (B j)) x) :
    fieldDerivative T (frameDet Z B) x =
      ∑ j, replacementDet Z B (fderiv ℝ (Z (B j)) x (T x)) j x := by
  let D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
    { Matrix.detRowAlternating.toMultilinearMap with cont := continuous_id.matrix_det }
  have hY := hasFDerivAt_pi.mpr (fun j => (hZ j).hasFDerivAt)
  have hd := (D.hasFDerivAt (fun j => Z (B j) x)).comp x hY
  have hfun : (fun y => D (fun j => Z (B j) y)) = frameDet Z B := by
    funext y
    exact Matrix.det_transpose (frameMatrix Z B y)
  change HasFDerivAt (fun y => D (fun j => Z (B j) y))
    ((D.linearDeriv (fun j => Z (B j) x)).comp
      (ContinuousLinearMap.pi (fun j => fderiv ℝ (Z (B j)) x))) x at hd
  rw [hfun] at hd
  rw [fieldDerivative, hd.fderiv]
  change D.linearDeriv (fun j => Z (B j) x) (fun j => fderiv ℝ (Z (B j)) x (T x)) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro j hj
  change ((frameMatrix Z B x).transpose.updateRow j
    (fderiv ℝ (Z (B j)) x (T x))).det = _
  rw [← Matrix.det_transpose, Matrix.updateRow_transpose, Matrix.transpose_transpose]
  rfl

/-- The determinant derivative is divergence times determinant
plus the column bracket replacements, with the BB sign convention
(BB Lemma 9.37, pp. 428–430). -/
theorem fieldDerivative_frameDet_bracket {ι : Type*} {n : ℕ}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} (B : Fin n → ι)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hZ : ∀ j, DifferentiableAt ℝ (Z (B j)) x) :
    fieldDerivative T (frameDet Z B) x =
      Hormander.Interface.euclideanDivergence T x * frameDet Z B x +
        ∑ j, replacementDet Z B (VectorField.lieBracket ℝ T (Z (B j)) x) j x := by
  rw [fieldDerivative_frameDet B T hZ]
  have hs : ∀ j, fderiv ℝ (Z (B j)) x (T x) =
      VectorField.lieBracket ℝ T (Z (B j)) x + fderiv ℝ T x (Z (B j) x) := by
    intro j
    simp only [VectorField.lieBracket]
    abel
  simp_rw [hs, replacementDet, Matrix.det_updateCol_add]
  rw [Finset.sum_add_distrib]
  have hlin : (∑ j, ((frameMatrix Z B x).updateCol j (fderiv ℝ T x (Z (B j) x))).det) =
      Hormander.Interface.euclideanDivergence T x * frameDet Z B x := by
    let A := LinearMap.toMatrix' (fderiv ℝ T x).toLinearMap
    have hcol : ∀ j, fderiv ℝ T x (Z (B j) x) = fun k => (A * frameMatrix Z B x) k j := by
      intro j
      exact (LinearMap.toMatrix'_mulVec (fderiv ℝ T x).toLinearMap (Z (B j) x)).symm
    simp_rw [hcol]
    exact sum_det_updateCol_mul (frameMatrix Z B x) A
  rw [hlin]
  exact add_comm _ _

end RothschildStein.G4
