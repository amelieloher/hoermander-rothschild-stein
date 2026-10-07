-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.RemainderFrameCoefficients
public import RothschildStein.G4.SuboptimalLowerBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Dividing an order-(d+s) remainder by the selected order-d
frame lower bound leaves the required signed radius weight (BB p. 444).
There is exactly one inverse-suboptimality factor. -/
theorem weighted_remainder_quotient_bound {d s : ℕ} {p : ℤ}
    (hp : p ≤ (s : ℤ)) {A e r t Δ D R : ℝ}
    (hA : 0 ≤ A) (he : 0 ≤ e) (hr : 0 < r) (hr1 : r ≤ 1)
    (ht : 0 < t) (hΔ : 0 < Δ)
    (hD : t * Δ * r ^ d ≤ D) (hR : R ≤ A * (e * r) ^ (d + s)) :
    R / D ≤ (A / (t * Δ)) * e ^ (d + s) * r ^ p := by
  have hbase : 0 < t * Δ * r ^ d := by positivity
  have hDpos : 0 < D := hbase.trans_le hD
  have hnum : 0 ≤ A * (e * r) ^ (d + s) := by positivity
  have hrp : r ^ s ≤ r ^ p := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hr1 hp
  calc
    R / D ≤ (A * (e * r) ^ (d + s)) / D :=
      div_le_div_of_nonneg_right hR hDpos.le
    _ ≤ (A * (e * r) ^ (d + s)) / (t * Δ * r ^ d) :=
      div_le_div_of_nonneg_left hnum hbase hD
    _ = (A / (t * Δ)) * e ^ (d + s) * r ^ s := by
      rw [mul_pow, pow_add r]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hrp (by positivity)

/-- Actual remainder frame coefficients have the target signed
weight once norm and selected determinant bounds are supplied. -/
theorem frameCoefficient_weighted_remainder_le {ι : Type*} {n d s : ℕ} {p : ℤ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (x : Fin n → ℝ)
    (hp : p ≤ (s : ℤ)) {H A e r t Δ : ℝ}
    (hZ : ∀ J k, |Z J x k| ≤ H)
    (hA : 0 ≤ A) (he : 0 ≤ e) (hr : 0 < r) (hr1 : r ≤ 1)
    (ht : 0 < t) (hΔ : 0 < Δ)
    (hdet : t * Δ * r ^ d ≤ |frameDet Z B x|)
    (hV : ‖V x‖ ≤ A * (e * r) ^ (d + s)) :
    |frameCoefficient Z B V i x| ≤
      (((n : ℝ) * n.factorial * (max H 1) ^ n) * A / (t * Δ)) *
        e ^ (d + s) * r ^ p := by
  have hb := frameCoefficient_remainder_norm_le Z B V i x
    (by positivity : 0 < t * Δ * r ^ d) hZ hdet
  have hP : 0 ≤ (n : ℝ) * n.factorial * (max H 1) ^ n := by positivity
  have hscaled := weighted_remainder_quotient_bound hp hA he hr hr1 ht hΔ
    (le_refl (t * Δ * r ^ d)) hV
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hscaled hP
  convert hh using 1 <;> ring

end RothschildStein.G4
