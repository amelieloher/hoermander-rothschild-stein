-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LpBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Strict distribution bound from the square integral. -/
theorem distribution_le_square_integral (μ : Measure X) (f : X → ℝ)
    (hf : AEMeasurable f μ) {t : ℝ} (ht : 0 < t) :
    distribution μ f t ≤ (ENNReal.ofReal (t ^ 2))⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hm : distribution μ f t ≤ μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := by
    apply measure_mono
    intro x hx
    change ENNReal.ofReal t ≤ ‖f x‖ₑ
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
  have hc := chebyshev_ennreal_power μ hf.enorm (by norm_num : (0 : ℝ) < 2) ht
  simp only [Real.rpow_two, ENNReal.rpow_two] at hc
  calc
    _ ≤ μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := hm
    _ = (ENNReal.ofReal (t ^ 2))⁻¹ *
        (ENNReal.ofReal (t ^ 2) * μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hc

/-- The good-part energy estimate yields the coefficient 4a/α. -/
theorem distribution_half_le_of_square_bound (μ : Measure X) (f : X → ℝ)
    (hf : AEMeasurable f μ) {α a : ℝ} (hα : 0 < α) (_ha : 0 ≤ a) (M : ℝ≥0∞)
    (henergy : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) ≤ ENNReal.ofReal (a * α) * M) :
    distribution μ f (α / 2) ≤ ENNReal.ofReal (4 * a / α) * M := by
  calc
    _ ≤ (ENNReal.ofReal ((α / 2) ^ 2))⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ :=
      distribution_le_square_integral μ f hf (by positivity)
    _ ≤ (ENNReal.ofReal ((α / 2) ^ 2))⁻¹ * (ENNReal.ofReal (a * α) * M) :=
      mul_le_mul' le_rfl henergy
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < (α / 2) ^ 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((α / 2) ^ 2)⁻¹)]
      congr 2
      field_simp
      ring

end RothschildStein.H2
