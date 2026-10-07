-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.PersistentCoefficientBounds
public import RothschildStein.G4.ActualLocalInverseFrameDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual inverse linear derivative on any short field is
bounded by its Cramer expansion in the selected frame. Intermediate
radius weights cancel exactly (BB Prop 9.52, (9.51), p. 448). -/
theorem frame_linearMap_weighted_field_bound {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {y : Fin n → ℝ}
    (hdet : frameDet Z B y ≠ 0) {r D L : ℝ} (hr : 0 < r) (hD : 0 ≤ D) (_hL : 0 ≤ L)
    (hframe : ∀ J j, |frameCoefficient Z B (Z J) j y| ≤
      D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)))
    (hT : ∀ i j, |T (Z (B j) y) i| ≤
      L * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ))) :
    ∀ J i, |T (Z J y) i| ≤
      (n : ℝ) * D * L * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) := by
  intro J i
  have hrep := frame_representation Z B (Z J) hdet
  have hval : T (Z J y) i = ∑ j, frameCoefficient Z B (Z J) j y * T (Z (B j) y) i := by
    conv_lhs => rw [hrep, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hval]
  calc
    _ ≤ ∑ j, |frameCoefficient Z B (Z J) j y * T (Z (B j) y) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, D * L * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply (mul_le_mul (hframe J j) (hT i j) (abs_nonneg _) (by positivity)).trans_eq
      calc
        _ = (D * L) * (r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) *
          r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ))) := by ring
        _ = _ := by rw [← zpow_add₀ hr.ne']; congr 2; omega
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A short control velocity of cost at most 2br has inverse
coordinate speed bounded by one numerical constant times b r^weight.
Every positive control weight contributes at least one small b factor
(BB Prop 9.52, (9.50)–(9.51), pp. 448–449). -/
theorem weighted_control_inverse_coordinate_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {y : Fin n → ℝ}
    (hdet : frameDet Z B y ≠ 0) {r b D L : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : 2 * b ≤ 1) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hframe : ∀ J j, |frameCoefficient Z B (Z J) j y| ≤
      D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)))
    (hT : ∀ i j, |T (Z (B j) y) i| ≤
      L * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)))
    (a : ι → ℝ) (ha : ∀ J, |a J| ≤ (2 * b * r) ^ (w J : ℕ)) :
    ∀ i, |T (∑ J, a J • Z J y) i| ≤
      (2 * (Fintype.card ι : ℝ) * n * D * L) * b * r ^ (w (B i) : ℕ) := by
  intro i
  have hfield := frame_linearMap_weighted_field_bound Z w B T hdet hr hD hL hframe hT
  have hval : T (∑ J, a J • Z J y) i = ∑ J, a J * T (Z J y) i := by
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hval]
  calc
    _ ≤ ∑ J, |a J * T (Z J y) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _J : ι, ((n : ℝ) * D * L) * (2 * b) * r ^ (w (B i) : ℕ) := by
      apply Finset.sum_le_sum
      intro J hJ
      rw [abs_mul]
      apply (mul_le_mul (ha J) (hfield J i) (abs_nonneg _) (by positivity)).trans
      have hpow : (2 * b) ^ (w J : ℕ) ≤ 2 * b :=
        pow_le_of_le_one (by positivity) hb1 (by have := (w J).pos; omega)
      have hrad : r ^ (w J : ℕ) *
          r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) = r ^ (w (B i) : ℕ) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr.ne']
        congr 1
        omega
      calc
        _ = ((n : ℝ) * D * L) * (2 * b) ^ (w J : ℕ) *
          (r ^ (w J : ℕ) * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ))) := by
            rw [mul_pow]; ring
        _ = ((n : ℝ) * D * L) * (2 * b) ^ (w J : ℕ) * r ^ (w (B i) : ℕ) := by rw [hrad]
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end RothschildStein.G4
