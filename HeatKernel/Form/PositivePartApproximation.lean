-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-!
# Differentiable approximation of the positive part

The primitive of a smooth transition from zero to one approximates the positive part. Its
derivative vanishes on the nonpositive half-line, including the corner at zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped Topology

namespace HeatKernel

/-- A differentiable approximation of the positive part at positive scale. -/
def positivePartApproximation (ε s : ℝ) : ℝ :=
  ∫ t in 0..s, smoothTransition (t / ε)

/-- The derivative of the approximation is the scaled smooth transition. -/
theorem hasDerivAt_positivePartApproximation (ε s : ℝ) :
    HasDerivAt (positivePartApproximation ε) (smoothTransition (s / ε)) s := by
  have hc : Continuous (fun t : ℝ => smoothTransition (t / ε)) :=
    smoothTransition.continuous.comp (continuous_id.div_const ε)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The positive-part approximation is continuously differentiable. -/
theorem contDiff_one_positivePartApproximation (ε : ℝ) :
    ContDiff ℝ 1 (positivePartApproximation ε) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun s => (hasDerivAt_positivePartApproximation ε s).differentiableAt, ?_⟩
  have he : deriv (positivePartApproximation ε) = fun s => smoothTransition (s / ε) :=
    funext fun s => (hasDerivAt_positivePartApproximation ε s).deriv
  rw [he]
  exact smoothTransition.continuous.comp (continuous_id.div_const ε)

/-- Its derivative has absolute value at most one. -/
theorem norm_deriv_positivePartApproximation_le (ε s : ℝ) :
    ‖deriv (positivePartApproximation ε) s‖ ≤ 1 := by
  rw [(hasDerivAt_positivePartApproximation ε s).deriv,
    Real.norm_of_nonneg (smoothTransition.nonneg _)]
  exact smoothTransition.le_one _

/-- At positive scale the approximation vanishes on the nonpositive half-line. -/
theorem positivePartApproximation_of_nonpos {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ 0) :
    positivePartApproximation ε s = 0 := by
  unfold positivePartApproximation
  rw [intervalIntegral.integral_symm]
  have H : (∫ t in s..0, smoothTransition (t / ε)) = ∫ _ in s..0, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs
    intro t ht
    exact smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht.2.le hε.le)
  rw [H, intervalIntegral.integral_zero, neg_zero]

/-- Beyond the transition interval the error from the identity is bounded by the scale. -/
theorem norm_positivePartApproximation_sub_le {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    ‖positivePartApproximation ε s - s‖ ≤ ε := by
  have hc : Continuous (fun t : ℝ => smoothTransition (t / ε)) :=
    smoothTransition.continuous.comp (continuous_id.div_const ε)
  have H : (∫ t in ε..s, smoothTransition (t / ε)) = s - ε := by
    calc
      _ = ∫ _ in ε..s, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs
        intro t ht
        exact smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith [ht.1]))
      _ = s - ε := by simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 ε) (hc.intervalIntegrable ε s)
  rw [H] at hsplit
  have he : positivePartApproximation ε s - s =
      ∫ t in 0..ε, (smoothTransition (t / ε) - 1) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
    unfold positivePartApproximation
    linarith
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := ε)
    (C := 1) (fun t _ => (show ‖smoothTransition (t / ε) - 1‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [smoothTransition.nonneg (t / ε), smoothTransition.le_one (t / ε)]))
  simpa only [one_mul, sub_zero, abs_of_pos hε] using hb

/-- Positive scales tending to zero give pointwise convergence to the positive part. -/
theorem tendsto_positivePartApproximation {ε : ℕ → ℝ}
    (hpos : ∀ n, 0 < ε n) (ht : Tendsto ε atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun n => positivePartApproximation (ε n) s) atTop (𝓝 (max s 0)) := by
  by_cases hs : s ≤ 0
  · simpa only [fun n => positivePartApproximation_of_nonpos (hpos n) hs, max_eq_right hs]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hs' : 0 < s := lt_of_not_ge hs
    have hev : ∀ᶠ n in atTop, ‖positivePartApproximation (ε n) s - s‖ ≤ ε n :=
      (ht.eventually (eventually_lt_nhds hs')).mono fun n hn =>
        norm_positivePartApproximation_sub_le (hpos n) hn.le
    have H : Tendsto (fun n => ‖positivePartApproximation (ε n) s - s‖) atTop (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hev ht
    rw [max_eq_left hs'.le]
    exact tendsto_iff_norm_sub_tendsto_zero.mpr H

/-- The derivatives converge to the strict positive-half-line indicator, including at zero. -/
theorem tendsto_deriv_positivePartApproximation {ε : ℕ → ℝ}
    (hpos : ∀ n, 0 < ε n) (ht : Tendsto ε atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun n => deriv (positivePartApproximation (ε n)) s) atTop
      (𝓝 (if 0 < s then (1 : ℝ) else 0)) := by
  by_cases hs : 0 < s
  · rw [ite_eq_left hs]
    apply tendsto_const_nhds.congr'
    apply (ht.eventually (eventually_lt_nhds hs)).mono
    intro n hn
    change 1 = deriv (positivePartApproximation (ε n)) s
    rw [(hasDerivAt_positivePartApproximation (ε n) s).deriv,
      smoothTransition.one_of_one_le ((le_div_iff₀ (hpos n)).mpr (by linarith))]
  · rw [ite_eq_right hs]
    apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro n
    change 0 = deriv (positivePartApproximation (ε n)) s
    rw [(hasDerivAt_positivePartApproximation (ε n) s).deriv,
      smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hs) (hpos n).le)]

end HeatKernel
