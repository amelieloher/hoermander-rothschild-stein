-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LowerTruncatedLogarithm
public import HeatKernel.Sobolev.LowerTruncatedRealPower
import Mathlib.Tactic

/-! # Zero-preserving logarithmic and power shifts -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal
namespace HeatKernel.Sobolev

/-- A shifted real power, constant on negative inputs and normalized to vanish at zero. -/
def zeroPreservingShiftedRpow (c p s : ℝ) : ℝ := lowerTruncatedRpow c p (s+c) - c^p

/-- Normalization and translation preserve the real-power Lipschitz constant. -/
theorem lipschitzWith_zeroPreservingShiftedRpow {c p : ℝ} (hc : 0 < c) (hp : p ≤ 1) :
    LipschitzWith (Real.toNNReal (|p| * c^(p-1))) (zeroPreservingShiftedRpow c p) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simpa only [zeroPreservingShiftedRpow, dist_sub_right, dist_add_right] using
    (lipschitzWith_lowerTruncatedRpow hc hp).dist_le_mul (s+c) (t+c)

/-- The normalized real-power shift fixes zero. -/
theorem zeroPreservingShiftedRpow_zero (c p : ℝ) : zeroPreservingShiftedRpow c p 0 = 0 := by
  simp only [zeroPreservingShiftedRpow, lowerTruncatedRpow, zero_add, max_self, sub_self]

/-- The real-power shift is C¹ away from the zero level. -/
theorem contDiffAt_zeroPreservingShiftedRpow {c p s : ℝ} (hc : 0 < c) (hs : s ≠ 0) :
    ContDiffAt ℝ 1 (zeroPreservingShiftedRpow c p) s := by
  have hsc : s+c ≠ c := by intro h; apply hs; linarith
  exact ((contDiffAt_lowerTruncatedRpow hc hsc).comp s
    (contDiffAt_id.add contDiffAt_const)).sub contDiffAt_const

/-- On nonnegative inputs the power shift is the literal centered real power. -/
theorem zeroPreservingShiftedRpow_eq {c p s : ℝ} (hs : 0 ≤ s) :
    zeroPreservingShiftedRpow c p s = (s+c)^p - c^p := by
  simp only [zeroPreservingShiftedRpow, lowerTruncatedRpow,
    max_eq_right (le_add_of_nonneg_left hs)]

end HeatKernel.Sobolev
