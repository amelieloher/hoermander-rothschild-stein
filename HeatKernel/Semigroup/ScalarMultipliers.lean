-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Scalar multipliers for the heat semigroup

The change of variable `r = (1 + a)⁻¹` represents a nonnegative operator by its bounded
resolvent. The corresponding heat multiplier extends continuously by zero at `r = 0`.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- The continuous heat multiplier at positive time, extended by zero on the negative axis. -/
def heatMultiplier (t r : ℝ) : ℝ := Real.exp t * expNegInvGlue (r / t)

/-- The bounded resolvent multiplier. -/
def resolventMultiplier (scale r : ℝ) : ℝ := r / (r + scale * (1 - r))

@[simp] theorem heatMultiplier_zero (t : ℝ) : heatMultiplier t 0 = 0 := by
  simp [heatMultiplier]

theorem heatMultiplier_of_pos {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    heatMultiplier t r = Real.exp (-t * (r⁻¹ - 1)) := by
  rw [heatMultiplier, expNegInvGlue, ite_eq_right (not_le.mpr (div_pos hr ht)), ← Real.exp_add]
  congr 1
  simp only [inv_div]
  ring

theorem heatMultiplier_of_nonpos {t r : ℝ} (ht : 0 < t) (hr : r ≤ 0) :
    heatMultiplier t r = 0 := by
  simp [heatMultiplier, expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr ht.le)]

theorem continuous_heatMultiplier (t : ℝ) : Continuous (heatMultiplier t) := by
  exact continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp
    (continuous_id.div_const t))

theorem heatMultiplier_nonneg (t r : ℝ) : 0 ≤ heatMultiplier t r :=
  mul_nonneg (Real.exp_pos t).le (expNegInvGlue.nonneg _)

theorem heatMultiplier_le_one {t r : ℝ} (ht : 0 < t) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    heatMultiplier t r ≤ 1 := by
  rcases eq_or_lt_of_le hr.1 with h | h
  · simp [← h]
  rw [heatMultiplier_of_pos ht h, Real.exp_le_one_iff]
  have hi : 1 ≤ r⁻¹ := (one_le_inv₀ h).mpr hr.2
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (sub_nonneg.mpr hi)

theorem heatMultiplier_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (r : ℝ) :
    heatMultiplier (s + t) r = heatMultiplier s r * heatMultiplier t r := by
  by_cases hr : 0 < r
  · rw [heatMultiplier_of_pos (add_pos hs ht) hr, heatMultiplier_of_pos hs hr,
      heatMultiplier_of_pos ht hr, ← Real.exp_add]
    congr 1
    ring
  · simp [heatMultiplier_of_nonpos hs (not_lt.mp hr),
      heatMultiplier_of_nonpos ht (not_lt.mp hr),
      heatMultiplier_of_nonpos (add_pos hs ht) (not_lt.mp hr)]

theorem resolventMultiplier_denominator_pos {scale r : ℝ} (hscale : 0 < scale)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) : 0 < r + scale * (1 - r) := by
  rcases eq_or_lt_of_le hr.1 with h | h
  · simp [← h, hscale]
  · exact add_pos_of_pos_of_nonneg h (mul_nonneg hscale.le (sub_nonneg.mpr hr.2))

theorem continuousOn_resolventMultiplier {scale : ℝ} (hscale : 0 < scale) :
    ContinuousOn (resolventMultiplier scale) (Set.Icc (0 : ℝ) 1) := by
  refine continuousOn_id.div
    (continuousOn_id.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))) ?_
  intro r hr
  exact (resolventMultiplier_denominator_pos hscale hr).ne'

@[simp] theorem resolventMultiplier_zero (scale : ℝ) : resolventMultiplier scale 0 = 0 := by
  simp [resolventMultiplier]

end HeatKernel
