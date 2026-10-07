-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.DerivativeFacts
public import Hormander.D.Defs

@[expose] public section

noncomputable section

namespace Hormander.B

/-- Peetre's inequality in the displayed Japanese-bracket ratio form. -/
theorem peetreRatio {N : ℕ} (x y : Carrier N) (s : ℝ) :
    japBracket x ^ s / japBracket y ^ s ≤
      (2 : ℝ) ^ (|s| / 2) * japBracket (x - y) ^ |s| := by
  have hp := peetre_jap x y s
  have hy : 0 < japBracket y ^ s := Real.rpow_pos_of_pos (japBracket_pos y) s
  calc
    japBracket x ^ s / japBracket y ^ s ≤ peetreOmega (x - y) ^ |s| := by
      apply (div_le_iff₀ hy).2
      simpa [mul_comm] using hp
    _ = (2 : ℝ) ^ (|s| / 2) * japBracket (x - y) ^ |s| := by
      rw [peetreOmega, Real.mul_rpow (Real.sqrt_nonneg 2) (japBracket_pos _).le,
        Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring

/-- Multipliers compose by multiplying their Schwartz coefficients. -/
theorem multiplierOperator_comp {N : ℕ} (g h : TestFunction N) :
    (multiplierOperator g).comp (multiplierOperator h) =
      multiplierOperator (multiplierOperator g h) := by
  ext u x
  simp only [LinearMap.comp_apply, multiplierOperator_apply]
  ring

/-- The outer multiplier is absorbed when it is one on the support of the inner coefficient. -/
theorem multiplierOperator_absorption {N : ℕ} (g h : TestFunction N)
    (hh : ∀ x ∈ tsupport g, h x = 1) :
    (multiplierOperator g).comp (multiplierOperator h) = multiplierOperator g := by
  ext u x
  simp only [LinearMap.comp_apply, multiplierOperator_apply]
  by_cases hg : g x = 0
  · simp [hg]
  · have hx : x ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hg)
    rw [hh x hx, one_mul]

theorem complexifyRealSchwartz_apply {N : ℕ} (g : SchwartzMap (Carrier N) ℝ)
    (x : Carrier N) : complexifyRealSchwartz g x = (g x : ℂ) := rfl

/-- Peetre's inequality and the order-zero Schwartz multiplier theorem. -/
theorem peetre_and_multiplier_order {N : ℕ} :
    (∀ (x y : Carrier N) (s : ℝ), japBracket x ^ s / japBracket y ^ s ≤
      (2 : ℝ) ^ (|s| / 2) * japBracket (x - y) ^ |s|) ∧
    (∀ g : TestFunction N, HasOrder 0 (multiplierOperator g)) :=
  ⟨peetreRatio, hasOrder_multiplierOperator_zero⟩

end Hormander.B
