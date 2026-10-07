-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualFrameInverseColumns

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual chart derivative sends a coordinate velocity to
its selected-field control vector through identity plus Cramer error. -/
theorem actual_chart_tangent_representation {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {y : Fin n → ℝ}
    (hdet : frameDet Z B y ≠ 0) (h : Fin n → ℝ) :
    let E : Matrix (Fin n) (Fin n) ℝ := fun j i => frameCoefficient Z B
      (fun _ => T (Pi.single i 1) - Z (B i) y) j y
    T h = ∑ j, (h j + E.mulVec h j) • Z (B j) y := by
  intro E
  have hfactor : coordinateDerivativeMatrix T = frameMatrix Z B y * (1 + E) :=
    coordinateDerivativeMatrix_frame_factorization Z B T hdet
  rw [← coordinateDerivativeMatrix_mulVec T h, hfactor,
    ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  ext k
  simp only [Matrix.mulVec, dotProduct, frameMatrix, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Signed radius powers cancel in the tangent error, leaving a
single dimension factor and the original small coordinate-speed factor
(BB Prop 9.55, p. 457). -/
theorem weighted_tangent_control_bound {n : ℕ} (w : Fin n → ℕ+)
    (E : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    {r κ C : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) (_hC : 0 ≤ C)
    (hE : ∀ j i, |E j i| ≤ κ * r ^ (((w j : ℕ) : ℤ) - ((w i : ℕ) : ℤ)))
    (hh : ∀ i, |h i| ≤ C * r ^ (w i : ℕ)) :
    ∀ j, |h j + E.mulVec h j| ≤ (1 + (n : ℝ) * κ) * C * r ^ (w j : ℕ) := by
  intro j
  have hterm : ∀ i, |E j i * h i| ≤ κ * C * r ^ (w j : ℕ) := by
    intro i
    rw [abs_mul]
    apply (mul_le_mul (hE j i) (hh i) (abs_nonneg _) (by positivity)).trans_eq
    calc
      _ = κ * C * (r ^ (((w j : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) *
        r ^ (w i : ℕ)) := by ring
      _ = κ * C * r ^ (w j : ℕ) := by
        rw [← zpow_natCast, ← zpow_add₀ hr.ne', sub_add_cancel, zpow_natCast]
  have herr : |E.mulVec h j| ≤ (n : ℝ) * κ * C * r ^ (w j : ℕ) := by
    change |∑ i, E j i * h i| ≤ _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun i _ => hterm i)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring)
  calc
    _ ≤ |h j| + |E.mulVec h j| := abs_add_le _ _
    _ ≤ C * r ^ (w j : ℕ) + (n : ℝ) * κ * C * r ^ (w j : ℕ) := add_le_add (hh j) herr
    _ = _ := by ring

end RothschildStein.G4
