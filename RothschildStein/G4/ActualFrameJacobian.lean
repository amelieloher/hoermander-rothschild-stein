-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import RothschildStein.G4.JacobianMatrixBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Columns of the actual derivative in the coordinate basis. -/
def coordinateDerivativeMatrix {n : ℕ}
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  fun k j => T (Pi.single j 1) k

/-- The actual derivative factors through the endpoint frame and
identity plus its actual Cramer error coordinates (BB Prop 9.50, p. 445).
The error matrix is defined from T; no matrix factorization is assumed. -/
theorem coordinateDerivativeMatrix_frame_factorization {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {y : Fin n → ℝ}
    (hdet : frameDet Z B y ≠ 0) :
    let E : Matrix (Fin n) (Fin n) ℝ := fun i j => frameCoefficient Z B
      (fun _ => T (Pi.single j 1) - Z (B j) y) i y
    coordinateDerivativeMatrix T = frameMatrix Z B y * (1 + E) := by
  intro E
  classical
  ext k j
  have he := frame_representation Z B
    (fun _ => T (Pi.single j 1) - Z (B j) y) hdet
  have hk := congrFun he k
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  change T (Pi.single j 1) k = ∑ i, Z (B i) y k *
    ((if i = j then 1 else 0) + frameCoefficient Z B
      (fun _ => T (Pi.single j 1) - Z (B j) y) i y)
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left]
  change T (Pi.single j 1) k = Z (B j) y k +
    ∑ i, Z (B i) y k * frameCoefficient Z B
      (fun _ => T (Pi.single j 1) - Z (B j) y) i y
  rw [show (∑ i, Z (B i) y k * frameCoefficient Z B
      (fun _ => T (Pi.single j 1) - Z (B j) y) i y) =
      ∑ i, frameCoefficient Z B (fun _ => T (Pi.single j 1) - Z (B j) y) i y *
        Z (B i) y k from Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  linarith

end RothschildStein.G4
