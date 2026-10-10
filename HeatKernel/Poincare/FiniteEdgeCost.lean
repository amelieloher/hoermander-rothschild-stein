-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Ring

/-! Real-valued forms of finite nonnegative Whitney edge costs. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal ENNReal

namespace HeatKernel

/-- A finite nonnegative extended-real edge estimate is the corresponding real estimate. -/
theorem abs_sub_le_of_nonnegative_weighted_edge_cost {c d a b K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K) (h₁ h₂ : ℝ≥0)
    (hbound : ENNReal.ofReal |c - d| ≤ ENNReal.ofReal K *
      (ENNReal.ofReal a * h₁ + ENNReal.ofReal b * h₂)) :
    |c - d| ≤ K * (a * (h₁ : ℝ) + b * (h₂ : ℝ)) := by
  have hn₁ : 0 ≤ a * (h₁ : ℝ) := mul_nonneg ha h₁.2
  have hn₂ : 0 ≤ b * (h₂ : ℝ) := mul_nonneg hb h₂.2
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (add_nonneg hn₁ hn₂))).mp
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_add hn₁ hn₂,
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_coe_nnreal]
  exact hbound

/-- The two homogeneous root factors in the edge bound combine to the finite real
coefficient 60 times the square of the root of 2^Q. -/
theorem homogeneous_edge_coefficient_eq_ofReal (Q : ℕ) {p : ℝ} (hp : 0 < p) :
    (((2 : ℝ≥0∞) ^ Q) ^ (1 / p) * ENNReal.ofReal (60 * ((2 : ℝ) ^ Q) ^ (1 / p))) =
      ENNReal.ofReal (60 * (((2 : ℝ) ^ Q) ^ (1 / p)) ^ 2) := by
  have hpow : (2 : ℝ≥0∞) ^ Q = ENNReal.ofReal ((2 : ℝ) ^ Q) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hpow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr hp.le),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  congr 1
  ring

end HeatKernel
