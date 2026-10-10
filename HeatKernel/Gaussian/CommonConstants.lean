-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # A single pair of Gaussian constants

Separate positive upper and lower constants can be replaced by one ordered pair,
chosen before the time and spatial variables. The harmless unit constants ensure
the order without additional comparisons between the original constants.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel.Gaussian

/-- Uniform upper and lower Gaussian estimates share a single positive ordered
pair of constants, independently of the indexing variables. -/
theorem exists_common_gaussian_constants {ι : Type*} (p S d : ι → ℝ)
    {a A b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hS : ∀ i, 0 ≤ S i) (hd : ∀ i, 0 ≤ d i)
    (hlower : ∀ i, b * S i * Real.exp (-B * d i) ≤ p i)
    (hupper : ∀ i, p i ≤ A * S i * Real.exp (-a * d i)) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ i,
      c * S i * Real.exp (-C * d i) ≤ p i ∧
        p i ≤ C * S i * Real.exp (-c * d i) := by
  let c := min 1 (min a b)
  let C := max 1 (max A B)
  have hc : 0 < c := lt_min zero_lt_one (lt_min ha hb)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hca : c ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  have hAC : A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : B ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c, C, hc, (min_le_left _ _).trans (le_max_left _ _), fun i => ⟨?_, ?_⟩⟩
  · apply le_trans _ (hlower i)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hcb (hS i)
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hBC) (hd i)
    · exact Real.exp_nonneg _
    · exact mul_nonneg hb.le (hS i)
  · apply le_trans (hupper i)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hAC (hS i)
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hca) (hd i)
    · exact Real.exp_nonneg _
    · exact mul_nonneg hC.le (hS i)

end HeatKernel.Gaussian
