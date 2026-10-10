-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderIteration
import Mathlib.Tactic

/-! # Absorbing terminal values in fixed small-power mean-value estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter
open scoped BigOperators
namespace HeatKernel

/-- A contraction chosen against the geometric cutoff growth has total error twice
its initial error. The terminal values are required to have a finite uniform bound. -/
theorem le_two_mul_of_geometric_absorption {S : ℕ → ℝ} {A D N H : ℝ}
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hN : 0 ≤ N)
    (hstep : ∀ j, S j ≤ (2 * A)⁻¹ * S (j + 1) + D * A ^ j * N)
    (hbound : ∀ j, S j ≤ H) : S 0 ≤ 2 * D * N := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hq : 0 ≤ (2 * A)⁻¹ := by positivity
  have hqone : (2 * A)⁻¹ < 1 :=
    (inv_lt_one₀ (by positivity : 0 < 2 * A)).mpr (by linarith)
  have hratio : (2 * A)⁻¹ * A = (1 / 2 : ℝ) := by field_simp
  have he : (fun j : ℕ => ((2 * A)⁻¹) ^ j * (D * A ^ j * N)) =
      (fun j : ℕ => (D * N) * (1 / 2 : ℝ) ^ j) := by
    funext j
    calc
      _ = (D * N) * (((2 * A)⁻¹) ^ j * A ^ j) := by ring
      _ = _ := by rw [← mul_pow, hratio]
  have hs : Summable (fun j : ℕ => ((2 * A)⁻¹) ^ j * (D * A ^ j * N)) := by
    rw [he]
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left (D * N)
  have h := le_tsum_of_contraction_of_bounded hq hqone
    (fun j => mul_nonneg (mul_nonneg hD (pow_nonneg hApos.le j)) hN) hstep hbound hs
  rw [he, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)] at h
  norm_num at h
  nlinarith

end HeatKernel
