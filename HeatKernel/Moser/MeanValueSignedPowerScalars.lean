-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueHalfPowerEnergy
import Mathlib.Tactic

/-! # Positive-power energy tests on signed values -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The positive-power transform vanishes on the nonpositive half-line. -/
theorem linearTailPositivePower_eq_zero_of_nonpos {M γ s : ℝ}
    (hM : 0 < M) (hγ : 0 < γ) (hs : s ≤ 0) :
    linearTailPositivePower M γ s = 0 := by
  simp only [linearTailPositivePower, boundedPositivePower,
    max_eq_left hs, min_eq_right hM.le, Real.zero_rpow hγ.ne',
    max_eq_left (show s - M ≤ 0 by linarith), mul_zero, add_zero]

/-- The normalized primitive also vanishes on the nonpositive half-line. -/
theorem linearTailPowerWeakSolutionTest_primitive_eq_zero_of_nonpos
    {M γ s : ℝ} (hM : 0 < M) (hγ : 1 ≤ γ) (hs : s ≤ 0) :
    (linearTailPowerWeakSolutionTest hM hγ).primitive s = 0 := by
  change (∫ t in (0 : ℝ)..s, linearTailPositivePower M γ t) = 0
  calc
    _ = ∫ t in (0 : ℝ)..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht0 : t ≤ 0 := (uIcc_of_ge hs ▸ ht).2
      exact linearTailPositivePower_eq_zero_of_nonpos hM (by linarith only [hγ]) ht0
    _ = 0 := by simp only [intervalIntegral.integral_zero]

/-- Positive-power tests and their primitives depend only on the positive part. -/
theorem linearTailPowerWeakSolutionTest_positive_part {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) :
    linearTailPositivePower M γ (max s 0) = linearTailPositivePower M γ s ∧
      (linearTailPowerWeakSolutionTest hM hγ).primitive (max s 0) =
        (linearTailPowerWeakSolutionTest hM hγ).primitive s := by
  rcases le_total 0 s with hs | hs
  · simp only [max_eq_left hs, and_self]
  · rw [max_eq_right hs, linearTailPositivePower_zero hM.le (by linarith only [hγ]),
      linearTailPositivePower_eq_zero_of_nonpos hM (by linarith only [hγ]) hs,
      linearTailPowerWeakSolutionTest_primitive_eq_zero_of_nonpos hM hγ le_rfl,
      linearTailPowerWeakSolutionTest_primitive_eq_zero_of_nonpos hM hγ hs]
    exact ⟨rfl, rfl⟩

/-- The truncated positive-part primitive controls its half-power for signed arguments. -/
theorem linearTailPositivePower_half_sq_le_primitive_signed {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) :
    linearTailPositivePower M (p / 2) s ^ 2 ≤
      p * (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).primitive s := by
  have h := linearTailPositivePower_half_sq_le_primitive hM hp (le_max_right s 0)
  rw [(linearTailPowerWeakSolutionTest_positive_part hM
    (show 1 ≤ p / 2 by linarith only [hp])).1,
    (linearTailPowerWeakSolutionTest_positive_part hM
      (show 1 ≤ p - 1 by linarith only [hp])).2] at h
  exact h

/-- The positive-part primitive is bounded by half the squared half-power, for any sign. -/
theorem linearTailPowerWeakSolutionTest_primitive_le_half_sq_signed {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) :
    (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p - 1 by linarith)).primitive s ≤
        linearTailPositivePower M (p / 2) s ^ 2 / 2 := by
  have h := linearTailPowerWeakSolutionTest_primitive_le_half_sq hM hp (le_max_right s 0)
  rw [(linearTailPowerWeakSolutionTest_positive_part hM
    (show 1 ≤ p / 2 by linarith only [hp])).1,
    (linearTailPowerWeakSolutionTest_positive_part hM
      (show 1 ≤ p - 1 by linarith only [hp])).2] at h
  exact h

end HeatKernel
