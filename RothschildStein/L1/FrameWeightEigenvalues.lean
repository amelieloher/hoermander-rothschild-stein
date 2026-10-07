-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Order.GroupWithZero.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- A linear map diagonal on a nonzero frame has the product of those
frame eigenvalues as its determinant. -/
theorem determinant_of_frame_eigenvectors {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι) (x : Fin n → ℝ)
    (hB : G4.frameDet Z B x ≠ 0) (D : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (eigen : Fin n → ℝ) (hD : ∀ j, D (Z (B j) x) = eigen j • Z (B j) x) :
    D.toMatrix'.det = ∏ j, eigen j := by
  classical
  have hmat : D.toMatrix' * G4.frameMatrix Z B x =
      G4.frameMatrix Z B x * Matrix.diagonal eigen := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrFun (hD j) i
    rw [← LinearMap.toMatrix'_mulVec] at hh
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, G4.frameMatrix,
      mul_comm] using hh
  have hh := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hh
  exact mul_right_cancel₀ hB (by simpa [G4.frameDet, mul_comm] using hh)

/-- Two nonzero frames diagonalizing the same dilation have equal total
natural weight. The dilation parameter two separates all natural powers. -/
theorem frame_weight_eq_of_dilation {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (weight : ι → ℕ)
    (B C : Fin n → ι) (x : Fin n → ℝ)
    (hB : G4.frameDet Z B x ≠ 0) (hC : G4.frameDet Z C x ≠ 0)
    (D : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hD : ∀ I, D (Z I x) = (2 : ℝ) ^ weight I • Z I x) :
    (∑ j, weight (B j)) = ∑ j, weight (C j) := by
  have hb := determinant_of_frame_eigenvectors Z B x hB D
    (fun j => (2 : ℝ) ^ weight (B j)) (fun j => hD (B j))
  have hc := determinant_of_frame_eigenvectors Z C x hC D
    (fun j => (2 : ℝ) ^ weight (C j)) (fun j => hD (C j))
  rw [Finset.prod_pow_eq_pow_sum] at hb hc
  exact (pow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).injective (hb.symm.trans hc)

end RothschildStein.L1
