-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSmallPowerYoung
public import HeatKernel.Moser.MeanValueSmallPowerAbsorption
import Mathlib.Tactic

/-! # Fixed small-power iteration with explicit absorption constants -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- A mixed small-power estimate on nested domains yields a bound independent of
terminal values. The finite terminal bound and the mixed estimate are explicit inputs. -/
theorem le_of_bounded_mixed_power_iteration {S : ℕ → ℝ} {F B N H θ : ℝ}
    (hF : 0 ≤ F) (hB : 1 ≤ B) (hN : 0 ≤ N)
    (hθ : 0 < θ) (hθone : θ < 1) (hS : ∀ j, 0 ≤ S j)
    (hstep : ∀ j, S j ≤ F * B ^ j * (S (j + 1)) ^ θ * N ^ (1 - θ))
    (hbound : ∀ j, S j ≤ H) :
    let A := B ^ (1 / (1 - θ))
    let ε := (2 * A)⁻¹
    S 0 ≤ 2 * (F / ε ^ θ) ^ (1 / (1 - θ)) * N := by
  intro A ε
  have hβ : 0 < 1 - θ := sub_pos.mpr hθone
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hA : 1 ≤ A := Real.one_le_rpow hB (by positivity)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεpow : 0 < ε ^ θ := Real.rpow_pos_of_pos hε _
  let D := (F / ε ^ θ) ^ (1 / (1 - θ))
  have hD : 0 ≤ D := Real.rpow_nonneg (div_nonneg hF hεpow.le) _
  apply le_two_mul_of_geometric_absorption hA hD hN _ hbound
  intro j
  have hy := mixed_power_le_epsilon_mul_add
    (mul_nonneg hF (pow_nonneg hBpos.le j)) (hS (j + 1)) hN hθ hθone hε
  have he : ((F * B ^ j) / ε ^ θ) ^ (1 / (1 - θ)) = D * A ^ j := by
    rw [show (F * B ^ j) / ε ^ θ = (F / ε ^ θ) * B ^ j by ring,
      Real.mul_rpow (div_nonneg hF hεpow.le) (pow_nonneg hBpos.le j)]
    dsimp only [D, A]
    rw [← Real.rpow_natCast_mul hBpos.le, mul_comm (j : ℝ), Real.rpow_mul_natCast hBpos.le]
  exact (hstep j).trans (by simpa only [he, ε] using hy)

end HeatKernel
