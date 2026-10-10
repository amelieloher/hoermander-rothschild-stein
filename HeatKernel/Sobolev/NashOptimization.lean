-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Optimization of averaging estimates

An approximation error linear in the averaging radius and an inverse-power
bound on the average give a Nash inequality. All constants are scalar, so the
result applies to any metric measure space supplying the two estimates.
-/

@[expose] public section

namespace HeatKernel.Sobolev

/-- Balancing the two radius-dependent terms of an averaging estimate. -/
theorem le_of_radius_approximation {L C U W k : ℝ}
    (hU : 0 < U) (hW : 0 < W) (hk : 0 < k)
    (happrox : ∀ s : ℝ, 0 < s → L ≤ C * s * U + W * s ^ (-k)) :
    L ≤ (C + 1) * U ^ (k / (1 + k)) * W ^ (1 / (1 + k)) := by
  have hden : 1 + k ≠ 0 := by positivity
  have hratio := div_pos hW hU
  have h := happrox ((W / U) ^ (1 / (1 + k))) (Real.rpow_pos_of_pos hratio _)
  have he : 1 / (1 + k) * (-k) = 1 / (1 + k) - 1 := by
    field_simp
    ring
  have he' : 1 - 1 / (1 + k) = k / (1 + k) := by
    field_simp
    ring
  have hlow : (W / U) ^ (1 / (1 + k)) * U =
      U ^ (k / (1 + k)) * W ^ (1 / (1 + k)) := by
    rw [Real.div_rpow hW.le hU.le, ← he', Real.rpow_sub hU, Real.rpow_one]
    ring
  have hhigh : W * ((W / U) ^ (1 / (1 + k))) ^ (-k) =
      U ^ (k / (1 + k)) * W ^ (1 / (1 + k)) := by
    rw [← Real.rpow_mul hratio.le, he, Real.div_rpow hW.le hU.le,
      Real.rpow_sub hW, Real.rpow_sub hU, ← he', Real.rpow_sub hU,
      Real.rpow_one, Real.rpow_one]
    field_simp
  calc
    L ≤ C * ((W / U) ^ (1 / (1 + k))) * U +
        W * ((W / U) ^ (1 / (1 + k))) ^ (-k) := h
    _ = (C + 1) * U ^ (k / (1 + k)) * W ^ (1 / (1 + k)) := by
      rw [mul_assoc C, hlow, hhigh]
      ring

/-- The squared Nash estimate, with the quadratic energy bound made explicit. -/
theorem sq_le_nash_of_radius_approximation {L C U W E ν : ℝ}
    (hL : 0 ≤ L) (hU : 0 < U) (hW : 0 < W)
    (hν : 0 < ν) (henergy : U ^ 2 ≤ 2 * E)
    (happrox : ∀ s : ℝ, 0 < s → L ≤ C * s * U + W * s ^ (-ν / 2)) :
    L ^ 2 ≤ (C + 1) ^ 2 * (2 * E) ^ (ν / (ν + 2)) * W ^ (4 / (ν + 2)) := by
  have hν₂ : ν + 2 ≠ 0 := by positivity
  have h := le_of_radius_approximation hU hW (by positivity : 0 < ν / 2) (by
    intro s hs
    simpa only [neg_div] using happrox s hs)
  have he₁ : (ν / 2) / (1 + ν / 2) = ν / (ν + 2) := by field_simp; ring
  have he₂ : 1 / (1 + ν / 2) * 2 = 4 / (ν + 2) := by field_simp; ring
  have he₃ : ν / (ν + 2) * 2 = 2 * (ν / (ν + 2)) := by ring
  rw [he₁] at h
  have hs := pow_le_pow_left₀ hL h 2
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hU.le,
    ← Real.rpow_mul_natCast hW.le] at hs
  norm_num only [Nat.cast_ofNat] at hs
  rw [he₂, he₃, Real.rpow_mul hU.le, Real.rpow_two] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (sq_nonneg U) henergy (by positivity)) (sq_nonneg (C + 1)))
    (Real.rpow_nonneg hW.le _))

end HeatKernel.Sobolev
