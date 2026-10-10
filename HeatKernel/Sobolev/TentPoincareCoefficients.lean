-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Explicit coefficients in the two tent Poincaré estimates -/

@[expose] public section
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Combining the inner half-radius cost and the outer volume-ratio cost. -/
theorem tent_poincare_coefficient_eq (Q : ℕ) (P : ℝ≥0∞) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) :
    ENNReal.ofReal a * (P * ENNReal.ofReal (r / 2) ^ 2) +
      ENNReal.ofReal (1 + (2 : ℝ) ^ Q) * P * ENNReal.ofReal r ^ 2 =
      P * ENNReal.ofReal ((1 + (2 : ℝ) ^ Q + a / 4) * r ^ 2) := by
  calc
    _ = P * (ENNReal.ofReal a * ENNReal.ofReal ((r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ Q) * ENNReal.ofReal (r ^ 2)) := by
      rw [ENNReal.ofReal_pow (by positivity : 0 ≤ r / 2), ENNReal.ofReal_pow hr]
      ring
    _ = P * ENNReal.ofReal (a * (r / 2) ^ 2 + (1 + (2 : ℝ) ^ Q) * r ^ 2) := by
      rw [← ENNReal.ofReal_mul ha,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + (2 : ℝ) ^ Q),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by congr 2; ring

/-- The linear-tent coefficient is dimension cost plus five quarters. -/
theorem linear_tent_poincare_coefficient_eq (Q : ℕ) (P : ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) :
    P * ENNReal.ofReal (r / 2) ^ 2 +
      ENNReal.ofReal (1 + (2 : ℝ) ^ Q) * P * ENNReal.ofReal r ^ 2 =
      P * ENNReal.ofReal (((2 : ℝ) ^ Q + 5 / 4) * r ^ 2) := by
  have H := tent_poincare_coefficient_eq Q P hr (by norm_num : (0 : ℝ) ≤ 1)
  norm_num only [ENNReal.ofReal_one, one_mul] at H
  have he : 1 + (2 : ℝ) ^ Q + 1 / 4 = (2 : ℝ) ^ Q + 5 / 4 := by ring
  simpa only [he] using H

/-- The squared-tent coefficient is dimension cost plus seven quarters. -/
theorem squared_tent_poincare_coefficient_eq (Q : ℕ) (P : ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) :
    3 * (P * ENNReal.ofReal (r / 2) ^ 2) +
      ENNReal.ofReal (1 + (2 : ℝ) ^ Q) * P * ENNReal.ofReal r ^ 2 =
      P * ENNReal.ofReal (((2 : ℝ) ^ Q + 7 / 4) * r ^ 2) := by
  have H := tent_poincare_coefficient_eq Q P hr (by norm_num : (0 : ℝ) ≤ 3)
  norm_num only [ENNReal.ofReal_ofNat] at H
  have he : 1 + (2 : ℝ) ^ Q + 3 / 4 = (2 : ℝ) ^ Q + 7 / 4 := by ring
  simpa only [he] using H

end HeatKernel.Sobolev
