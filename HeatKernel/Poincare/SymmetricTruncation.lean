-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel

/-- Symmetric scalar truncation is bounded by its truncation level. -/
theorem abs_symmetric_truncation_le_level {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    |max (-M) (min x M)| ≤ M := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Symmetric scalar truncation does not increase absolute value. -/
theorem abs_symmetric_truncation_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    |max (-M) (min x M)| ≤ |x| := by
  apply abs_le.mpr
  constructor
  · exact (le_min (neg_abs_le x) (by linarith [abs_nonneg x])).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_left _ _).trans (le_abs_self x))

/-- Symmetric truncation fixes values lying between its two levels. -/
theorem symmetric_truncation_eq_self {M x : ℝ} (h : |x| ≤ M) :
    max (-M) (min x M) = x := by
  obtain ⟨hl, hr⟩ := abs_le.mp h
  rw [min_eq_left hr, max_eq_right hl]

/-- Symmetric truncations can be expressed using two shifted positive parts. -/
theorem symmetric_truncation_eq_positive_parts {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    max (-M) (min x M) = x - max (x - M) 0 + max (-x - M) 0 := by
  by_cases hx : x ≤ M
  · rw [min_eq_left hx, max_eq_right (sub_nonpos.mpr hx)]
    by_cases hl : -M ≤ x
    · rw [max_eq_right hl, max_eq_right (by linarith : -x - M ≤ 0)]
      simp
    · rw [max_eq_left (le_of_not_ge hl), max_eq_left (by linarith : 0 ≤ -x - M)]
      ring
  · have hxM : M ≤ x := le_of_not_ge hx
    rw [min_eq_right hxM, max_eq_right (by linarith : -M ≤ M),
      max_eq_left (sub_nonneg.mpr hxM), max_eq_right (by linarith : -x - M ≤ 0)]
    ring

/-- Truncation at natural levels eventually fixes each real value. -/
theorem eventually_symmetric_truncation_eq (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, max (-(n : ℝ)) (min x n) = x := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  exact symmetric_truncation_eq_self (hN.trans (by exact_mod_cast hn))

/-- Symmetric truncations tend pointwise to the identity. -/
theorem tendsto_symmetric_truncation (x : ℝ) :
    Tendsto (fun n : ℕ => max (-(n : ℝ)) (min x n)) atTop (𝓝 x) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_symmetric_truncation_eq x] with n hn
  exact hn.symm

/-- Removing both exterior positive-part gradients restricts a scalar derivative
to the symmetric truncation interval. -/
theorem symmetric_truncation_gradient_identity {M : ℝ} (hM : 0 ≤ M) (x a : ℝ) :
    a - (if M < x then a else 0) + (if M < -x then -a else 0) =
      if |x| ≤ M then a else 0 := by
  by_cases hu : M < x
  · have hl : ¬ M < -x := by linarith
    have ha : ¬ |x| ≤ M := by
      intro h
      exact (not_lt_of_ge ((le_abs_self x).trans h)) hu
    simp only [ite_eq_left hu, ite_eq_right hl, ite_eq_right ha, sub_self, add_zero]
  · by_cases hl : M < -x
    · have ha : ¬ |x| ≤ M := by
        intro h
        have := (abs_le.mp h).1
        linarith
      simp only [ite_eq_right hu, ite_eq_left hl, ite_eq_right ha, sub_zero, add_neg_cancel]
    · have ha : |x| ≤ M := abs_le.mpr ⟨by linarith, le_of_not_gt hu⟩
      simp only [ite_eq_right hu, ite_eq_right hl, ite_eq_left ha, sub_zero, add_zero]

end HeatKernel
