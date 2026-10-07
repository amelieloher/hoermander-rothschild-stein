-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- The chain rule for the fiber parametrization gives
its vertical Jacobian as the full Jacobian divided by the horizontal
Jacobian (BB pp. 520–521, equations 10.45–10.49). -/
theorem vertical_jacobian_det_of_block_chain {n m : ℕ}
    (A : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin m) (Fin m) ℝ)
    (hchain : A * Matrix.fromBlocks H⁻¹ C 0 1 = Matrix.fromBlocks 1 0 D V) :
    V.det = A.det / H.det := by
  classical
  have hh := congrArg Matrix.det hchain
  simpa only [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, one_mul,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv, div_eq_mul_inv] using hh.symm

end RothschildStein.L1
