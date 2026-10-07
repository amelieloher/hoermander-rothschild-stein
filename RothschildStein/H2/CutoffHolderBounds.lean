-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalHolderNorm
public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- The explicit cutoff seminorm bound on a ball, using its diameter
bound 2r rather than any special metric-ball diameter equality. BB p. 308. -/
theorem KernelCutoff.holderSemi_ball_le {U : Set X} {L : ℝ≥0} {b : X → ℝ}
    (hb : KernelCutoff U L b) {z : X} {r : ℝ} (hr : 0 < r)
    {γ : ℝ≥0} (hγ : γ ≤ 1) :
    holderSemi γ (ball z r) b ≤ ENNReal.ofReal ((L : ℝ) * (2 * r) ^ (1 - (γ : ℝ))) := by
  apply holderSemi_le_of_bound (mul_nonneg L.coe_nonneg (Real.rpow_nonneg (by linarith) _))
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, abs_zero, dist_self]
    exact mul_nonneg (mul_nonneg L.coe_nonneg (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by norm_num) _)
  have hd := dist_pos.mpr hxy
  have hp := rpow_gain_le (α := (γ : ℝ)) (ν := 1) hd (dist_lt_two_radius hx hy).le (show (γ : ℝ) ≤ 1 from hγ)
  rw [Real.rpow_one] at hp
  have he := hb.lipschitz.dist_le_mul x y
  rw [Real.dist_eq] at he
  have he' := mul_le_mul_of_nonneg_left hp L.coe_nonneg
  nlinarith

/-- The full explicit cutoff Hölder norm on a ball. -/
theorem KernelCutoff.holderNorm_ball_le {U : Set X} {L : ℝ≥0} {b : X → ℝ}
    (hb : KernelCutoff U L b) {z : X} {r : ℝ} (hr : 0 < r)
    {γ : ℝ≥0} (hγ : γ ≤ 1) :
    boundedHolderNorm γ (ball z r) b ≤ ENNReal.ofReal (1 + (L : ℝ) * (2 * r) ^ (1 - (γ : ℝ))) := by
  have hs : holderSup (ball z r) b ≤ ENNReal.ofReal 1 := holderSup_le_of_bound (by
    intro x _
    rw [abs_of_nonneg (hb.nonneg x)]
    exact hb.le_one x)
  have hh := hb.holderSemi_ball_le (z := z) hr hγ
  exact (add_le_add hs hh).trans_eq (ENNReal.ofReal_add (by norm_num)
    (mul_nonneg L.coe_nonneg (Real.rpow_nonneg (by linarith) _))).symm

/-- Every Data D cutoff is bounded Hölder on each ball. -/
theorem KernelCutoff.boundedHolder_ball {U : Set X} {L : ℝ≥0} {b : X → ℝ}
    (hb : KernelCutoff U L b) {z : X} {r : ℝ} (hr : 0 < r)
    {γ : ℝ≥0} (hγ : γ ≤ 1) : BoundedHolder γ (ball z r) b :=
  (hb.holderNorm_ball_le hr hγ).trans_lt ENNReal.ofReal_lt_top

end RothschildStein.H2
