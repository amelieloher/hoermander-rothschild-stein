-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Module.Determinant

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Module

namespace RothschildStein.L1

/-- Ordinary derivative matrix in the product coordinate
basis, with the horizontal block preceding the vertical block. -/
def productDerivativeMatrix {n m : ℕ}
    (L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin m → ℝ))) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  LinearMap.toMatrix ((Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin m)))
    ((Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin m))) L.toLinearMap

/-- The product derivative matrix consists of the four actual partial
coordinate derivatives. -/
theorem productDerivativeMatrix_eq_blocks {n m : ℕ}
    (L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin m → ℝ))) :
    productDerivativeMatrix L = Matrix.fromBlocks
      (((ContinuousLinearMap.fst ℝ _ _).comp (L.comp (ContinuousLinearMap.inl ℝ _ _))).toLinearMap.toMatrix')
      (((ContinuousLinearMap.fst ℝ _ _).comp (L.comp (ContinuousLinearMap.inr ℝ _ _))).toLinearMap.toMatrix')
      (((ContinuousLinearMap.snd ℝ _ _).comp (L.comp (ContinuousLinearMap.inl ℝ _ _))).toLinearMap.toMatrix')
      (((ContinuousLinearMap.snd ℝ _ _).comp (L.comp (ContinuousLinearMap.inr ℝ _ _))).toLinearMap.toMatrix') := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp [productDerivativeMatrix, LinearMap.toMatrix_apply, Basis.prod_apply,
      Basis.prod_repr_inl, Basis.prod_repr_inr, Pi.basisFun_apply, Pi.basisFun_repr,
      LinearMap.toMatrix'_apply]

/-- The ordinary product derivative matrices multiply in the same
order as the actual chain rule. -/
theorem productDerivativeMatrix_comp {n m : ℕ}
    (A B : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin m → ℝ))) :
    productDerivativeMatrix (A.comp B) = productDerivativeMatrix A * productDerivativeMatrix B := by
  classical
  exact LinearMap.toMatrix_comp _ _ _ A.toLinearMap B.toLinearMap

/-- [L1-F1] The coordinate determinant is the actual linear derivative
determinant used by Mathlib's change-of-variables theorem. -/
theorem productDerivativeMatrix_det {n m : ℕ}
    (L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin m → ℝ))) :
    (productDerivativeMatrix L).det = L.det := by
  classical
  exact LinearMap.det_toMatrix _ L.toLinearMap

end RothschildStein.L1
