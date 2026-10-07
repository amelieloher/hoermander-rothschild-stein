-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualFrameJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- A dimension-only weighted derivative-error threshold gives
factor-four bounds for the determinant of the ACTUAL derivative. Its
error matrix is formed from Cramer coordinates; its factorization is
proved, and selected determinant persistence is used in both directions
(BB Proposition 9.50, pp. 445–446). -/
theorem exists_actual_frame_jacobian_threshold (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∀ (ι : Type*) (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
        (B : Fin n → ι) (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (x y : Fin n → ℝ) (r : ℝ), 0 < r → frameDet Z B x ≠ 0 →
      |frameDet Z B y - frameDet Z B x| ≤ |frameDet Z B x| / 2 →
      (∀ i j, |frameCoefficient Z B (fun z => T (Pi.single j 1) - Z (B j) z) i y| ≤
        κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ))) →
      |frameDet Z B x| / 4 ≤ |Matrix.det (coordinateDerivativeMatrix T)| ∧
        |Matrix.det (coordinateDerivativeMatrix T)| ≤ 4 * |frameDet Z B x| := by
  obtain ⟨κ, hκ, hsmall, hthreshold⟩ := exists_weighted_determinant_threshold n
  refine ⟨κ, hκ, hsmall, ?_⟩
  intro ι Z w B T x y r hr hx hpersist herror
  have htri : |frameDet Z B x| ≤ |frameDet Z B y - frameDet Z B x| + |frameDet Z B y| := by
    simpa only [sub_add_cancel, abs_sub_comm] using
      abs_add_le (frameDet Z B x - frameDet Z B y) (frameDet Z B y)
  have hhalf : |frameDet Z B x| / 2 ≤ |frameDet Z B y| := by linarith
  have hupper : |frameDet Z B y| ≤ 2 * |frameDet Z B x| := by
    have hh := abs_add_le (frameDet Z B y - frameDet Z B x) (frameDet Z B x)
    rw [sub_add_cancel] at hh
    linarith [abs_nonneg (frameDet Z B x)]
  have hy : frameDet Z B y ≠ 0 := abs_pos.mp
    ((half_pos (abs_pos.mpr hx)).trans_le hhalf)
  let E : Matrix (Fin n) (Fin n) ℝ := fun i j => frameCoefficient Z B
    (fun _ => T (Pi.single j 1) - Z (B j) y) i y
  have hE : ∀ i j, |E i j| ≤ κ * r ^ (w (B i) : ℕ) / r ^ (w (B j) : ℕ) := by
    intro i j
    have hb := herror i j
    rw [zpow_sub₀ hr.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc] at hb
    exact hb
  have hdet := hthreshold (fun i => (w (B i) : ℕ)) E r hr hE
  exact jacobian_determinant_bounds_of_matrix_factorization (frameMatrix Z B y) E
    (coordinateDerivativeMatrix T) (frameDet Z B x)
    (coordinateDerivativeMatrix_frame_factorization Z B T hy)
    ⟨hhalf, hupper⟩ hdet

end RothschildStein.G4
