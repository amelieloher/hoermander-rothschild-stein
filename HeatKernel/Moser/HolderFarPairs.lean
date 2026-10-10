-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Hölder comparison for pairs separated by a fixed fraction of the radius -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- An oscillation bound supplies the Hölder estimate for pairs whose separation
is at least one sixty-fourth of the reference radius. -/
theorem abs_sub_le_holder_of_separation
    {u v W δ r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (hδ : r / 64 ≤ δ) (huv : |u - v| ≤ W) :
    |u - v| ≤ (64 : ℝ) ^ a * (δ / r) ^ a * W := by
  have hratio : 1 ≤ 64 * (δ / r) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hr).mpr (by linarith)
  have hδ0 : 0 ≤ δ / r := by nlinarith
  have hpow : 1 ≤ (64 * (δ / r)) ^ a := Real.one_le_rpow hratio ha
  rw [Real.mul_rpow (by norm_num) hδ0] at hpow
  exact huv.trans (le_mul_of_one_le_left hW hpow)

end HeatKernel
