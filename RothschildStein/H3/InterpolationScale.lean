-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ScaledField

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3
open scoped ENNReal

/-- Cancellation of the positive finite step factor is valid
 even when some norms are infinite. -/
theorem interpolation_cancel_step {ε : ℝ} (hε : 0 < ε) (D U DD : ℝ≥0∞)
    (h : ENNReal.ofReal ε * D ≤ 2*U +
      ENNReal.ofReal (1/2 : ℝ) * (ENNReal.ofReal ε * ENNReal.ofReal ε * DD)) :
    D ≤ ENNReal.ofReal (2/ε) * U + ENNReal.ofReal (ε/2) * DD := by
  let a := ENNReal.ofReal ε
  let b := ENNReal.ofReal (1/2 : ℝ)
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have h1 : a⁻¹ * 2 = ENNReal.ofReal (2/ε) := by
    change (ENNReal.ofReal ε)⁻¹ * 2 = _
    rw [← ENNReal.ofReal_inv_of_pos hε, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hε.le)]
    congr 1
    simp only [div_eq_mul_inv,mul_comm]
  have h2 : a⁻¹ * (b*(a*a)) = ENNReal.ofReal (ε/2) := by
    calc
      a⁻¹ * (b*(a*a)) = b*(a⁻¹*a)*a := by ac_rfl
      _ = b*a := by rw [ENNReal.inv_mul_cancel ha0 hat,mul_one]
      _ = ENNReal.ofReal (ε/2) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
        congr 1
        ring
  calc
    D = a⁻¹*(a*D) := (ENNReal.inv_mul_cancel_left ha0 hat).symm
    _ ≤ a⁻¹*(2*U+b*(a*a*DD)) := by gcongr
    _ = ENNReal.ofReal (2/ε)*U + ENNReal.ofReal (ε/2)*DD := by
      calc
        a⁻¹*(2*U+b*(a*a*DD)) =
            (a⁻¹*2)*U + (a⁻¹*(b*(a*a)))*DD := by simp only [mul_add,mul_assoc]
        _ = _ := by rw [h1,h2]

end RothschildStein.H3
