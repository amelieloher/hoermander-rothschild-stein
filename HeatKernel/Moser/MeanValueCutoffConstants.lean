-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueIterationConstants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Cutoff losses in positive-power mean-value iteration -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- Polynomial cutoff losses become a linear logarithmic cost weighted geometrically. -/
theorem cutoff_iteration_factor_eq_exp {C B δ χ : ℝ}
    (hC : 0 < C) (hB : 0 < B) (hδ : 0 < δ) (hχ : 0 < χ) (j : ℕ) :
    (C * B ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j)) =
      Real.exp (((Real.log C - 2 * Real.log δ) / 2 +
        (Real.log B / 2) * (j : ℝ)) * (χ⁻¹) ^ j) := by
  rw [Real.rpow_def_of_pos (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul hC.ne' (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_pow]
  congr 1
  rw [inv_pow]
  field_simp
  ring

/-- The exact cutoff-product constant is finite and independent of the iteration index. -/
theorem le_cutoff_iteration_constant_mul {Y : ℕ → ℝ} {C B δ χ : ℝ}
    (hC : 1 ≤ C) (hB : 1 ≤ B) (hδ : 0 < δ) (hδone : δ ≤ 1) (hχ : 1 < χ)
    (hY : 0 ≤ Y 0)
    (hstep : ∀ j, Y (j + 1) ≤ (C * B ^ j / δ ^ 2) ^ (1 / (2 * χ ^ j)) * Y j)
    (n : ℕ) :
    Y n ≤ Real.exp (((Real.log C - 2 * Real.log δ) / 2) * (1 - χ⁻¹)⁻¹ +
      (Real.log B / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) * Y 0 := by
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  have ha : 0 ≤ (Real.log C - 2 * Real.log δ) / 2 := by
    have hc := Real.log_nonneg hC
    have hd := Real.log_nonpos hδ.le hδone
    linarith
  have hb : 0 ≤ Real.log B / 2 := div_nonneg (Real.log_nonneg hB) (by norm_num)
  apply le_exp_explicit_cost_mul_of_iteration (inv_nonneg.mpr hχpos.le)
    ((inv_lt_one₀ hχpos).mpr hχ) ha hb hY _ n
  intro j
  simpa only [cutoff_iteration_factor_eq_exp (zero_lt_one.trans_le hC)
    (zero_lt_one.trans_le hB) hδ hχpos] using hstep j

end HeatKernel
