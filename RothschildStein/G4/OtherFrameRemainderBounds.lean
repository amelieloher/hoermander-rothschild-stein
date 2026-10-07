-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TaylorPolynomialBounds
public import RothschildStein.G4.SuboptimalLowerBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The Taylor remainder of order 2ns uses the selected
order-ns denominator without additional inverse-suboptimality powers.
The signed frame-weight difference may be negative. -/
theorem other_frame_remainder_scale_bound {d : ℕ} (hd : 0 < d) {p : ℤ}
    (hp : p ≤ (d : ℤ)) {A e r t Δ D R : ℝ}
    (hA : 0 ≤ A) (he : 0 ≤ e) (he1 : e ≤ 1) (het : e ≤ t)
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) (hΔ : 0 < Δ)
    (hD : t * Δ * r ^ d ≤ D) (hR : R ≤ A * (e * r) ^ (2 * d)) :
    R ≤ (A / Δ) * r ^ p * D := by
  have hep : e ^ (2 * d) ≤ t :=
    (pow_le_of_le_one he he1 (by omega : 2 * d ≠ 0)).trans het
  have hrp : r ^ d ≤ r ^ p := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ hr hr1 hp
  have hD0 : 0 ≤ D := (mul_nonneg (mul_nonneg ht.le hΔ.le) (pow_nonneg hr.le _)).trans hD
  have hscaled := mul_le_mul_of_nonneg_left hD
    (mul_nonneg (div_nonneg hA hΔ.le) (pow_nonneg hr.le d))
  calc
    R ≤ A * (e * r) ^ (2 * d) := hR
    _ = A * e ^ (2 * d) * r ^ (2 * d) := by rw [mul_pow]; ring
    _ ≤ A * t * r ^ (2 * d) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hep hA) (pow_nonneg hr.le _)
    _ = ((A / Δ) * r ^ d) * (t * Δ * r ^ d) := by
      have htwo : 2 * d = d + d := by omega
      rw [htwo, pow_add]
      field_simp [ne_of_gt hΔ]
    _ ≤ (A / Δ) * r ^ d * D := hscaled
    _ ≤ (A / Δ) * r ^ p * D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrp (div_nonneg hA hΔ.le)) hD0

end RothschildStein.G4
