-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Scale-independent constants for the two logarithmic tails -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- The variance and mean-correction costs are uniformly bounded after division
by the reference cylinder mass. -/
theorem logarithmic_harnack_tail_cost_le
    {K S ell D r mass V δ δ₀ : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hell : 0 < ell) (hD : 0 ≤ D) (hr : 0 < r)
    (hmass : mass ≤ S * V) (hV : 0 ≤ V) (hδ : 0 ≤ δ)
    (hδr : δ ≤ 4 * r^2) (hδ₀ : r^2 ≤ δ₀) (hδδ₀ : δ ≤ δ₀) :
    max (324 * (K * (3 * r / 2)^2 / ell * mass))
      (2 * (D / (3 * r / 2)^2) * δ * (δ * V)) ≤
        (10000 * (K * S / ell + D)) * (δ₀ * V) := by
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hα : 0 ≤ K * S / ell := by positivity
  have hbase : 0 ≤ δ₀ * V := mul_nonneg (hr2.le.trans hδ₀) hV
  have hscale : r^2 * V ≤ δ₀ * V := mul_le_mul_of_nonneg_right hδ₀ hV
  apply max_le
  · calc
      324 * (K * (3 * r / 2)^2 / ell * mass) ≤
          324 * (K * (3 * r / 2)^2 / ell * (S * V)) := by
            gcongr
      _ = 729 * (K * S / ell) * (r^2 * V) := by ring
      _ ≤ 10000 * (K * S / ell) * (δ₀ * V) := by
        exact mul_le_mul (by nlinarith) hscale
          (mul_nonneg hr2.le hV) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hD hbase]
  · have hcost : 2 * (D / (3 * r / 2)^2) * δ ≤ 4 * D := by
      have heq : 2 * (D / (3 * r / 2)^2) * δ = (2 * D * δ) / (3 * r / 2)^2 := by ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < (3 * r / 2)^2)).mpr
      have H := mul_le_mul_of_nonneg_left hδr (by positivity : 0 ≤ 2 * D)
      nlinarith
    calc
      2 * (D / (3 * r / 2)^2) * δ * (δ * V) ≤ 4 * D * (δ₀ * V) :=
        mul_le_mul hcost (mul_le_mul_of_nonneg_right hδδ₀ hV)
          (mul_nonneg hδ hV) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hα hbase]

end HeatKernel
