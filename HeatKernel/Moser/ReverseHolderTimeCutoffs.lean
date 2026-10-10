-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueTimeCutoffs
import Mathlib.Tactic

/-! Smooth time cutoffs for energy estimates running backward in time. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace HeatKernel

/-- Reflection of the smooth lower-time transition gives a cutoff equal to one
before the inner top and zero from the outer top onward. The derivative of its
square has a bound uniform in both top times. -/
theorem exists_uniform_backward_time_cutoff_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, a < b → ∃ θ : ℝ → ℝ,
      ContDiff ℝ 1 θ ∧ (∀ t, θ t ∈ Icc (0 : ℝ) 1) ∧
      (∀ t, t ≤ a → θ t = 1) ∧ (∀ t, b ≤ t → θ t = 0) ∧
      ∀ t, -deriv (fun s => θ s ^ 2) t ≤ 2 * C / (b - a) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lowerTimeCutoff_derivative_bound
  refine ⟨C, hC, fun a b hab => ?_⟩
  let θ : ℝ → ℝ := fun t => lowerTimeCutoff (-b) (-a) (-t)
  have hθ : ContDiff ℝ 1 θ :=
    ((contDiff_lowerTimeCutoff (-b) (-a)).of_le (by simp)).comp contDiff_neg
  have hab' : -b < -a := neg_lt_neg hab
  refine ⟨θ, hθ, fun t => lowerTimeCutoff_mem_Icc _ _ _,
    fun t ht => lowerTimeCutoff_eq_one hab' (neg_le_neg ht),
    fun t ht => lowerTimeCutoff_eq_zero hab' (neg_le_neg ht), fun t => ?_⟩
  have hd := (((contDiff_lowerTimeCutoff (-b) (-a)).of_le (by simp) :
      ContDiff ℝ 1 (lowerTimeCutoff (-b) (-a))).differentiable (by norm_num)
        (-t)).hasDerivAt.comp t ((hasDerivAt_id t).neg)
  have hsq : deriv (fun s => θ s ^ 2) t =
      2 * θ t * (deriv (lowerTimeCutoff (-b) (-a)) (-t) * (-1)) := by
    have hdθ : HasDerivAt θ (deriv (lowerTimeCutoff (-b) (-a)) (-t) * (-1)) t := hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using (hdθ.fun_pow 2).deriv
  have hdle : deriv (lowerTimeCutoff (-b) (-a)) (-t) ≤ C / (b - a) := by
    have hn : deriv (lowerTimeCutoff (-b) (-a)) (-t) ≤
        ‖deriv (lowerTimeCutoff (-b) (-a)) (-t)‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    exact hn.trans (by convert hbound (-b) (-a) hab' (-t) using 1; ring)
  have hunit := lowerTimeCutoff_mem_Icc (-b) (-a) (-t)
  have hcost : 0 ≤ C / (b - a) := div_nonneg hC.le (sub_nonneg.mpr hab.le)
  rw [hsq]
  calc
    -(2 * θ t * (deriv (lowerTimeCutoff (-b) (-a)) (-t) * (-1))) =
        2 * θ t * deriv (lowerTimeCutoff (-b) (-a)) (-t) := by ring
    _ ≤ 2 * θ t * (C / (b - a)) :=
      mul_le_mul_of_nonneg_left hdle (mul_nonneg (by norm_num) hunit.1)
    _ ≤ 2 * (C / (b - a)) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith [hunit.2]) hcost
    _ = 2 * C / (b - a) := by ring

end HeatKernel
