-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueLinearTailTests
import Mathlib.Tactic

/-! # Exact primitive and energy bounds for linear-tail positive-power tests -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The linear-tail test is bounded above by the full positive power. -/
theorem linearTailPositivePower_le_rpow {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (hs : 0 ≤ s) :
    linearTailPositivePower M γ s ≤ s ^ γ := by
  rcases le_total s M with hsM | hMs
  · exact (linearTailPositivePower_eq_rpow hs hsM).le
  · rw [linearTailPositivePower_eq_linear hM hMs]
    have he : s ^ γ = s ^ (γ - 1) * s := by
      simpa only [sub_add_cancel, Real.rpow_one] using
        Real.rpow_add (hM.trans_le hMs) (γ - 1) 1
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hM.le hMs (sub_nonneg.mpr hγ)) hs

/-- Above the threshold the normalized primitive has an exact quadratic tail. -/
theorem linearTailPowerWeakSolutionTest_primitive_above {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (hs : M ≤ s) :
    (linearTailPowerWeakSolutionTest hM hγ).primitive s =
      M ^ (γ + 1) / (γ + 1) + M ^ (γ - 1) * (s ^ 2 - M ^ 2) / 2 := by
  have hc := (lipschitzWith_linearTailPositivePower hM.le hγ).continuous
  have he := linearTailPowerWeakSolutionTest_primitive hM hγ hM.le le_rfl
  change (∫ t in (0 : ℝ)..M, linearTailPositivePower M γ t) = _ at he
  change (∫ t in (0 : ℝ)..s, linearTailPositivePower M γ t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 M) (hc.intervalIntegrable M s), he]
  have ht : (∫ t in M..s, linearTailPositivePower M γ t) =
      M ^ (γ - 1) * (s ^ 2 - M ^ 2) / 2 := by
    calc
      _ = ∫ t in M..s, M ^ (γ - 1) * t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hs] at ht
        exact linearTailPositivePower_eq_linear hM ht.1
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [ht]

/-- On the upper tail the primitive controls the weighted quadratic energy with
the same normalization as the untruncated power. -/
theorem linearTailPowerWeakSolutionTest_quadratic_le_primitive {M γ s : ℝ}
    (hM : 0 < M) (hγ : 1 ≤ γ) (hs : M ≤ s) :
    s ^ 2 * M ^ (γ - 1) / (γ + 1) ≤
      (linearTailPowerWeakSolutionTest hM hγ).primitive s := by
  rw [linearTailPowerWeakSolutionTest_primitive_above hM hγ hs]
  have he : M ^ (γ + 1) = M ^ (γ - 1) * M ^ 2 := by
    have hp := Real.rpow_add hM (γ - 1) 2
    have hexp : γ - 1 + 2 = γ + 1 := by ring
    simpa only [hexp, Real.rpow_two] using hp
  rw [he]
  have hpos : 0 < γ + 1 := by linarith
  apply (div_le_iff₀ hpos).mpr
  have hc := div_mul_cancel₀ (M ^ (γ - 1) * M ^ 2) hpos.ne'
  have hg : 0 ≤ s ^ 2 - M ^ 2 := by nlinarith
  have hp : 0 ≤ M ^ (γ - 1) * (γ - 1) * (s ^ 2 - M ^ 2) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hM.le _) (sub_nonneg.mpr hγ)) hg
  nlinarith

end HeatKernel
