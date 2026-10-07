-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualFrameJacobian
public import RothschildStein.G4.WeightedInverseColumns

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- The coordinate derivative matrix acts as the actual derivative
on every vector in the coordinate space (BB Prop 9.50, p. 445). -/
theorem coordinateDerivativeMatrix_mulVec {n : ℕ}
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (u : Fin n → ℝ) :
    (coordinateDerivativeMatrix T).mulVec u = T u := by
  have hu : u = ∑ j, u j • (Pi.single j 1 : Fin n → ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_rhs => rw [hu, map_sum]
  ext i
  simp only [Matrix.mulVec, dotProduct, coordinateDerivativeMatrix, Finset.sum_apply,
    map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- The actual inverse derivative applied to an endpoint frame
column has the required signed coordinate bound. Any vector solving the
actual derivative equation is covered; no inverse matrix estimate is
assumed (BB Lemma 9.51, pp. 446–447). -/
theorem actual_frame_inverse_column_bound {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {y : Fin n → ℝ}
    (hdet : frameDet Z B y ≠ 0) {r κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ)
    (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (herror : ∀ i j, |frameCoefficient Z B (fun z => T (Pi.single j 1) - Z (B j) z) i y| ≤
      κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)))
    (u : Fin n → ℝ) (ℓ : Fin n) (hu : T u = Z (B ℓ) y) :
    ∀ i, |u i| ≤ (4 / 3 : ℝ) *
      r ^ (((w (B i) : ℕ) : ℤ) - ((w (B ℓ) : ℕ) : ℤ)) := by
  classical
  let E : Matrix (Fin n) (Fin n) ℝ := fun i j => frameCoefficient Z B
    (fun _ => T (Pi.single j 1) - Z (B j) y) i y
  have hfactor := coordinateDerivativeMatrix_frame_factorization Z B T hdet
  have hE : ∀ i j, |E i j| ≤ κ * r ^ (w (B i) : ℕ) / r ^ (w (B j) : ℕ) := by
    intro i j
    have hb := herror i j
    rw [zpow_sub₀ hr.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc] at hb
    exact hb
  have hunit : IsUnit (frameMatrix Z B y) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsol : (1 + E).mulVec u = Pi.single ℓ 1 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    rw [Matrix.mulVec_mulVec, ← hfactor, coordinateDerivativeMatrix_mulVec, hu]
    rw [Matrix.mulVec_single_one]
    rfl
  have hb := weighted_identity_add_inverse_column_bound (fun i => (w (B i) : ℕ)) E
    hr hκ hsmall hE u ℓ hsol
  intro i
  rw [zpow_sub₀ hr.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc]
  exact hb i

end RothschildStein.G4
