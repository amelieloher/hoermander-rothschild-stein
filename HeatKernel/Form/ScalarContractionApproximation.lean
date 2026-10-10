-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScalarSmoothing
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Smooth approximation of scalar contractions

Shrinking normalized bump convolutions, recentered at zero, approximate every scalar normal
contraction pointwise. All approximants are smooth normal contractions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Convolution Topology NNReal

namespace HeatKernel

/-- Every scalar normal contraction has smooth approximants fixing zero with derivative
bounded by one and pointwise convergence everywhere. -/
theorem exists_smooth_contraction_approximation {η : ℝ → ℝ}
    (hη : LipschitzWith 1 η) (hzero : η 0 = 0) :
    ∃ a : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (a n)) ∧
      (∀ n, a n 0 = 0) ∧ (∀ n s, ‖deriv (a n) s‖ ≤ 1) ∧
      ∀ s, Tendsto (fun n => a n s) atTop (𝓝 (η s)) := by
  let r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    { rIn := r n / 2
      rOut := r n
      rIn_pos := div_pos (hr n) (by norm_num)
      rIn_lt_rOut := by have H := hr n; linarith }
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ℕ → ℝ → ℝ := fun n s => smoothScalarAverage (φ n) η s - smoothScalarAverage (φ n) η 0
  have haLip : ∀ n, LipschitzWith 1 (a n) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [a, dist_sub_right] using
      (lipschitzWith_smoothScalarAverage (φ n) hη).dist_le_mul x y
  refine ⟨a, fun n => (contDiff_smoothScalarAverage (φ n) hη.continuous).sub contDiff_const,
    fun n => sub_self _, fun n s => ?_, fun s => ?_⟩
  · simpa only [NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := s) (haLip n)
  · have hs := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hη.continuous s
    have h0 := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hη.continuous 0
    simpa only [a, smoothScalarAverage, hzero, sub_zero] using hs.sub h0

end HeatKernel
