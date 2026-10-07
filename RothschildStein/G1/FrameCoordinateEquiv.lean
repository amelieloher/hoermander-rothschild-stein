-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.G1

/-- A nondegenerate actual bracket frame supplies the continuous
linear equivalence used by the quantitative inverse-function argument. -/
def frameCoordinateEquiv {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι) (x : Fin n → ℝ)
    (hB : G4.frameDet Z B x ≠ 0) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) (G4.frameMatrix Z B x)
    (isUnit_iff_ne_zero.mpr hB)).toContinuousLinearEquiv

/-- The frame equivalence uses exactly the actual selected columns. -/
theorem frameCoordinateEquiv_apply {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι) (x : Fin n → ℝ)
    (hB : G4.frameDet Z B x ≠ 0) (u : Fin n → ℝ) :
    frameCoordinateEquiv Z B x hB u = ∑ i, u i • Z (B i) x := by
  classical
  change Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
    (G4.frameMatrix Z B x) u = _
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  ext j
  simp only [Matrix.mulVec, dotProduct, G4.frameMatrix, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end RothschildStein.G1
