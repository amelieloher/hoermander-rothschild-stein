-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ProductDerivativeMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- A horizontal derivative with the parameter retained has
zero lower-left block and identity lower-right block. -/
theorem productDerivativeMatrix_parameter_retaining {n m : ℕ}
    (L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin n → ℝ)) :
    productDerivativeMatrix (L.prod (ContinuousLinearMap.snd ℝ _ _)) =
      Matrix.fromBlocks
        ((L.comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap.toMatrix')
        ((L.comp (ContinuousLinearMap.inr ℝ _ _)).toLinearMap.toMatrix') 0 1 := by
  rw [productDerivativeMatrix_eq_blocks]
  simp [← ContinuousLinearMap.comp_assoc]

/-- A derivative with the horizontal coordinate retained has
identity upper-left block and zero upper-right block. -/
theorem productDerivativeMatrix_base_retaining {n m : ℕ}
    (L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin m → ℝ)) :
    productDerivativeMatrix ((ContinuousLinearMap.fst ℝ _ _).prod L) =
      Matrix.fromBlocks 1 0
        ((L.comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap.toMatrix')
        ((L.comp (ContinuousLinearMap.inr ℝ _ _)).toLinearMap.toMatrix') := by
  rw [productDerivativeMatrix_eq_blocks]
  simp [← ContinuousLinearMap.comp_assoc]

/-- The matrix of the inverse actual horizontal derivative is
the ordinary nonsingular inverse of its coordinate matrix. -/
theorem toMatrix_continuousLinearEquiv_symm {n : ℕ}
    (H : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
    H.symm.toLinearEquiv.toLinearMap.toMatrix' = H.toLinearEquiv.toLinearMap.toMatrix'⁻¹ := by
  classical
  have he : H.toLinearEquiv.toLinearMap.comp H.symm.toLinearEquiv.toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro u
    exact H.apply_symm_apply u
  have hm : H.toLinearEquiv.toLinearMap.toMatrix' * H.symm.toLinearEquiv.toLinearMap.toMatrix' = 1 := by
    rw [← LinearMap.toMatrix'_comp, he, LinearMap.toMatrix'_id]
  exact (Matrix.inv_eq_right_inv hm).symm

end RothschildStein.L1
