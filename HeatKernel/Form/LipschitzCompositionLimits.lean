-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.DominatedL2
public import HeatKernel.Form.SmoothGraphLimits
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic.Linarith

/-! # L² limits of pointwise convergent scalar contractions -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace HeatKernel

/-- Pointwise convergence of scalar normal contractions gives strong L² convergence after
composition with a fixed L² function. -/
theorem tendsto_L2_of_contraction_pointwise {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℝ 2 μ) {a : ℕ → ℝ → ℝ} {η : ℝ → ℝ} {w : ℕ → Lp ℝ 2 μ}
    (ha : ∀ n, LipschitzWith 1 (a n)) (ha0 : ∀ n, a n 0 = 0)
    (hη : LipschitzWith 1 η) (hzero : η 0 = 0)
    (hat : ∀ s, Tendsto (fun n => a n s) atTop (𝓝 (η s)))
    (hw : ∀ n, w n =ᵐ[μ] fun x => a n (u x)) :
    Tendsto w atTop (𝓝 (hη.compLp hzero u)) := by
  have hanorm : ∀ n s, ‖a n s‖ ≤ ‖s‖ := by
    intro n s
    simpa only [ha0, dist_zero_right, NNReal.coe_one, one_mul] using (ha n).dist_le_mul s 0
  have hηnorm : ∀ s, ‖η s‖ ≤ ‖s‖ := by
    intro s
    simpa only [hzero, dist_zero_right, NNReal.coe_one, one_mul] using hη.dist_le_mul s 0
  apply tendsto_L2_of_representatives hw (hη.coeFn_compLp hzero u)
  apply tendsto_eLpNorm_two_zero_of_dominated
    (fun n => ((ha n).continuous.comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable).sub
      (hη.continuous.comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable))
    ((Lp.memLp u).norm.const_mul 2)
  · intro n
    apply Eventually.of_forall
    intro x
    simp only [Pi.sub_apply, Real.norm_of_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg (u x)))]
    have H := norm_sub_le (a n (u x)) (η (u x))
    linarith [hanorm n (u x), hηnorm (u x)]
  · exact Eventually.of_forall fun x => by
      simpa only [Pi.sub_apply, sub_self] using (hat (u x)).sub_const (η (u x))

end HeatKernel
