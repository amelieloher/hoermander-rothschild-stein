-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.ScalarBounds
import Mathlib.Tactic

/-! # Endpoint estimates and Gaussian decay

The two mean-value applications use cylinders strictly inside positive heat time.
Their squared pointwise estimate yields the Gaussian upper bound after taking a
square root and absorbing the linear exponential term.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
namespace HeatKernel.Gaussian

/-- The endpoint cylinder stays within positive times below three times the
endpoint separation, uniformly over the permitted central times. -/
theorem endpoint_cylinder_subset_positive {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Icc (t / 2) (2 * t)) :
    let r := Real.sqrt t / 4
    0 < s - 7 * r ^ 2 / 2 ∧
      Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2) ⊆ Ioo 0 (3 * t) := by
  dsimp
  have hsq := Real.sq_sqrt ht.le
  constructor
  · nlinarith [hs.1]
  · intro u hu
    constructor
    · nlinarith [hs.1, hu.1]
    · nlinarith [hs.2, hu.2]

/-- The second endpoint cylinder lies in the range where the first row estimate
is uniform. -/
theorem endpoint_cylinder_subset_row_times {t : ℝ} (ht : 0 < t) :
    let r := Real.sqrt t / 4
    Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2) ⊆ Icc (t / 2) (2 * t) := by
  dsimp
  have hsq := Real.sq_sqrt ht.le
  intro u hu
  constructor <;> nlinarith [hu.1, hu.2]

/-- Taking a square root in the two-endpoint pointwise estimate gives the stated
Gaussian decay, with an explicit constant for the absorbed linear loss. -/
theorem le_gaussian_of_squared_endpoint_bound {p M V a : ℝ}
    (hM : 0 ≤ M) (hV : 0 < V)
    (hbound : p ^ 2 ≤ (M / V) ^ 2 * Real.exp (-a ^ 2 / 6 + a / 3)) :
    p ≤ (M * Real.exp (1 / 6) / V) * Real.exp (-a ^ 2 / 24) := by
  let B := M / V * Real.exp (-a ^ 2 / 12 + a / 6)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsq : B ^ 2 = (M / V) ^ 2 * Real.exp (-a ^ 2 / 6 + a / 3) := by
    dsimp [B]
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  have hp : p ≤ B := by rw [← hsq] at hbound; nlinarith
  calc
    p ≤ B := hp
    _ ≤ M / V * (Real.exp (1 / 6) * Real.exp (-a ^ 2 / 24)) :=
      mul_le_mul_of_nonneg_left (exp_quadratic_linear_le a) (div_nonneg hM hV.le)
    _ = _ := by ring

/-- The normalized spatial distance has exactly the expected squared heat ratio. -/
theorem sq_div_sqrt {d t : ℝ} (ht : 0 ≤ t) :
    (d / Real.sqrt t) ^ 2 = d ^ 2 / t := by
  rw [div_pow, Real.sq_sqrt ht]

end HeatKernel.Gaussian
