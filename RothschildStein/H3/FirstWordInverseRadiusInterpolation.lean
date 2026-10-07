-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The inverse-radius interpolation parameter is admissible at every
radius at least the reciprocal of the fixed interpolation threshold. -/
theorem inverseRadius_interpolation_parameter {R δE : ℝ}
    (hR : 0 < R) (hδE : 0 < δE) (hlarge : δE⁻¹ ≤ R) :
    0 < R⁻¹ ∧ R⁻¹ ≤ δE := by
  refine ⟨inv_pos.mpr hR, ?_⟩
  have hh : 1 ≤ R * δE := (div_le_iff₀ hδE).mp (by simpa only [one_div] using hlarge)
  have hh' : 1 / R ≤ δE := (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hh)
  simpa only [one_div] using hh'

/-- Step 2: choosing delta=1/R in Phi interpolation cancels
all radius factors and gives the fixed first-derivative estimate. -/
theorem firstWord_bound_of_inverseRadius_interpolation
    {R D P₀ P₁ P₂ C₂ cE U : ℝ} (hR : 0 < R) (hcE : 0 ≤ cE)
    (hhalf : (R / 2) * D ≤ P₁)
    (hinterp : P₁ ≤ R⁻¹ * P₂ + (cE / R⁻¹) * P₀)
    (hsecond : P₂ ≤ (R ^ 2 / 4) * C₂) (hzero : P₀ ≤ U) :
    D ≤ C₂ / 2 + 2 * cE * U := by
  have hinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have hc : 0 ≤ cE / R⁻¹ := div_nonneg hcE hinv
  have hb : (R / 2) * D ≤ R⁻¹ * ((R ^ 2 / 4) * C₂) + (cE / R⁻¹) * U :=
    hhalf.trans (hinterp.trans (add_le_add
      (mul_le_mul_of_nonneg_left hsecond hinv) (mul_le_mul_of_nonneg_left hzero hc)))
  have he : R⁻¹ * ((R ^ 2 / 4) * C₂) + (cE / R⁻¹) * U =
      (R / 2) * (C₂ / 2 + 2 * cE * U) := by
    field_simp [hR.ne']; ring
  rw [he] at hb
  nlinarith

end RothschildStein.H3
