-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Calculus.FDeriv.Mul
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Negating a square coordinate derivative preserves its absolute determinant. -/
theorem abs_linear_det_neg {N : ℕ} (A : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) :
    |(-A).det| = |A.det| := by
  classical
  rw [← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix' A]
  have he : (-A).toMatrix' = -A.toMatrix' := by
    ext i j
    rfl
  rw [he, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Reversing canonical coordinates has unit absolute Jacobian factor. -/
theorem abs_fderiv_precompose_neg {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (u : Fin N → ℝ) (hf : DifferentiableAt ℝ f (-u)) :
    |(fderiv ℝ (fun v => f (-v)) u).det| = |(fderiv ℝ f (-u)).det| := by
  have hneg : HasFDerivAt (fun v : Fin N → ℝ => -v)
      (-ContinuousLinearMap.id ℝ (Fin N → ℝ)) u := (hasFDerivAt_id u).fun_neg
  have hd : HasFDerivAt (fun v => f (-v))
      ((fderiv ℝ f (-u)).comp (-ContinuousLinearMap.id ℝ (Fin N → ℝ))) u :=
    hf.hasFDerivAt.comp u hneg
  have he : (fderiv ℝ f (-u)).comp (-ContinuousLinearMap.id ℝ (Fin N → ℝ)) =
      -fderiv ℝ f (-u) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply, map_neg]
  rw [hd.fderiv, he]
  exact abs_linear_det_neg (fderiv ℝ f (-u)).toLinearMap
end RothschildStein.L1
