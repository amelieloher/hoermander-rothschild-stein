-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Explicit Young constants for fixed small-power estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- A mixed power estimate can be absorbed with any positive coefficient on the
larger essential supremum, with an explicit remaining constant. -/
theorem mixed_power_le_epsilon_mul_add {A x N θ ε : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hN : 0 ≤ N)
    (hθ : 0 < θ) (hθone : θ < 1) (hε : 0 < ε) :
    A * x ^ θ * N ^ (1 - θ) ≤
      ε * x + (A / ε ^ θ) ^ (1 / (1 - θ)) * N := by
  let D := (A / ε ^ θ) ^ (1 / (1 - θ))
  have hβ : 0 < 1 - θ := sub_pos.mpr hθone
  have hεpow : 0 < ε ^ θ := Real.rpow_pos_of_pos hε _
  have hD : 0 ≤ D := Real.rpow_nonneg (div_nonneg hA hεpow.le) _
  have hd : D ^ (1 - θ) = A / ε ^ θ := by
    dsimp [D]
    rw [← Real.rpow_mul (div_nonneg hA hεpow.le), one_div_mul_cancel hβ.ne', Real.rpow_one]
  have he : A * x ^ θ * N ^ (1 - θ) = (ε * x) ^ θ * (D * N) ^ (1 - θ) := by
    rw [Real.mul_rpow hε.le hx, Real.mul_rpow hD hN, hd]
    field_simp
  calc
    _ = _ := he
    _ ≤ θ * (ε * x) + (1 - θ) * (D * N) :=
      Real.geom_mean_le_arith_mean2_weighted hθ.le hβ.le
        (mul_nonneg hε.le hx) (mul_nonneg hD hN) (by ring)
    _ ≤ ε * x + D * N := by
      nlinarith [mul_nonneg hβ.le (mul_nonneg hε.le hx),
        mul_nonneg hθ.le (mul_nonneg hD hN)]

end HeatKernel
