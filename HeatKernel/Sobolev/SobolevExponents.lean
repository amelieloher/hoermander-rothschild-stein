-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SobolevFromNash
import Mathlib.Tactic

/-!
# Exponents in the subcritical Sobolev estimate

The dimension parameter is strictly above two. Choosing a smaller intermediate
parameter gives a larger weak exponent, leaving room for strong interpolation.
-/

@[expose] public section

namespace HeatKernel.Sobolev

/-- The Nash first-moment exponent is strictly between zero and one. -/
theorem nash_exponent_mem_Ioo {ν : ℝ} (hν : 2 < ν) :
    0 < 4 / (ν + 2) ∧ 4 / (ν + 2) < 1 := by
  have hd : 0 < ν + 2 := by linarith
  constructor
  · positivity
  · apply (div_lt_one hd).mpr
    linarith

/-- The energy exponent in the quadratic Nash inequality. -/
theorem nash_energy_exponent {ν : ℝ} (hν : 2 < ν) :
    1 - (4 / (ν + 2)) / 2 = ν / (ν + 2) := by
  have hd : ν + 2 ≠ 0 := by linarith
  field_simp
  ring

/-- Iterating Nash gives the expected weak Sobolev exponent. -/
theorem weakSobolevExponent_nash {ν : ℝ} (hν : 2 < ν) :
    weakSobolevExponent (4 / (ν + 2)) = 2 * ν / (ν - 2) := by
  unfold weakSobolevExponent
  have hd : ν + 2 ≠ 0 := by linarith
  have hden : 1 - 4 / (ν + 2) = (ν - 2) / (ν + 2) := by
    field_simp
    ring
  have hnum : 2 - 4 / (ν + 2) = 2 * ν / (ν + 2) := by
    field_simp
    ring
  rw [hden, hnum, div_div_div_cancel_right₀ hd]

/-- The strong Sobolev exponent exceeds two. -/
theorem two_lt_sobolevExponent {ν : ℝ} (hν : 2 < ν) :
    2 < 2 * ν / (ν - 2) := by
  apply (lt_div_iff₀ (by linarith : 0 < ν - 2)).mpr
  linarith

/-- Increasing the dimension parameter decreases the Sobolev exponent. -/
theorem sobolevExponent_lt_of_lt {ν' ν : ℝ} (hν' : 2 < ν') (hν : ν' < ν) :
    2 * ν / (ν - 2) < 2 * ν' / (ν' - 2) := by
  apply (div_lt_div_iff₀ (by linarith : 0 < ν - 2) (by linarith : 0 < ν' - 2)).mpr
  nlinarith

/-- The volume exponents add to one when the Sobolev estimate is normalized. -/
theorem sobolev_volume_exponent {ν : ℝ} (hν : 2 < ν) :
    2 / (2 * ν / (ν - 2)) + 2 / ν = 1 := by
  have hν₀ : ν ≠ 0 := by linarith
  have hd : ν - 2 ≠ 0 := by linarith
  field_simp
  ring

end HeatKernel.Sobolev
