-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Patches
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Dyadic iteration at decreasing radii stays within the patch range.
BB Lemma 7.4, pp. 296–297. -/
theorem DoublingPatch.iterate (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {s : ℝ} (hs : 0 < s) (hκ : s ≤ 6 * P.ρ) (n : ℕ) :
    P.μ (ball z s) ≤ ENNReal.ofReal P.C_D ^ n * P.μ (ball z (s / 2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    have hscale : s / 2 ^ n ≤ s :=
      div_le_self hs.le (one_le_pow₀ (by norm_num))
    have hd := (P.doubling z hz (s / 2 ^ n) (by positivity) (hscale.trans hκ)).2.2
    calc
      P.μ (ball z s) ≤ ENNReal.ofReal P.C_D ^ n * P.μ (ball z (s / 2 ^ n)) := ih
      _ ≤ ENNReal.ofReal P.C_D ^ n *
          (ENNReal.ofReal P.C_D * P.μ (ball z ((s / 2 ^ n) / 2))) :=
        mul_le_mul_right hd _
      _ = ENNReal.ofReal P.C_D ^ (n + 1) * P.μ (ball z (s / 2 ^ (n + 1))) := by
        rw [pow_succ, mul_assoc, div_div, pow_succ]

/-- A dyadic comparison with any adequate integer number of doublings. -/
theorem DoublingPatch.compare_pow (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {r s : ℝ} (_hr : 0 < r) (hs : 0 < s) (hκ : s ≤ 6 * P.ρ)
    (n : ℕ) (hscale : s ≤ 2 ^ n * r) :
    P.μ (ball z s) ≤ ENNReal.ofReal P.C_D ^ n * P.μ (ball z r) := by
  refine (P.iterate hz hs hκ n).trans (mul_le_mul_right (measure_mono
    (ball_subset_ball ?_)) _)
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).mpr (by nlinarith)

/-- The integer bound with ceiling log₂(s/r), including equal radii. -/
theorem DoublingPatch.compare (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hκ : s ≤ 6 * P.ρ) :
    P.μ (ball z s) ≤ ENNReal.ofReal P.C_D ^ ⌈Real.logb 2 (s / r)⌉₊ *
      P.μ (ball z r) := by
  have hs : 0 < s := hr.trans_le hrs
  apply P.compare_pow hz hr hs hκ
  have hlog : Real.logb 2 (s / r) ≤ (⌈Real.logb 2 (s / r)⌉₊ : ℝ) := Nat.le_ceil _
  have hd := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (div_pos hs hr)).mp hlog
  rw [Real.rpow_natCast] at hd
  exact (div_le_iff₀ hr).mp hd

end RothschildStein.H2
