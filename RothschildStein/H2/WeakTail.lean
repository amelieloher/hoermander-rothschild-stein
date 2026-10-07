-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LayerCake

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Separate the enlarged bad-ball union from its complement. -/
theorem distribution_restrict_le_exception (μ : Measure X) (U E : Set X)
    (hE : MeasurableSet E) (f : X → ℝ) (t : ℝ) :
    distribution (μ.restrict U) f t ≤ μ E + distribution (μ.restrict (U \ E)) f t := by
  unfold distribution
  rw [← Measure.restrict_inter_add_sdiff U hE, Measure.add_apply]
  apply add_le_add ?_ le_rfl
  calc
    _ ≤ (μ.restrict (U ∩ E)) univ := measure_mono (subset_univ _)
    _ = μ (U ∩ E) := Measure.restrict_apply_univ _
    _ ≤ μ E := measure_mono inter_subset_right

/-- Strict distribution bound from the L¹ integral. -/
theorem distribution_le_l1_integral (μ : Measure X) (f : X → ℝ)
    (hf : AEMeasurable f μ) {t : ℝ} (ht : 0 < t) :
    distribution μ f t ≤ (ENNReal.ofReal t)⁻¹ * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have hm : distribution μ f t ≤ μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := by
    apply measure_mono
    intro x hx
    change ENNReal.ofReal t ≤ ‖f x‖ₑ
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
  calc
    _ ≤ μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := hm
    _ = (ENNReal.ofReal t)⁻¹ *
        (ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl (chebyshev_ennreal μ hf.enorm _)

/-- A bad-part L¹ estimate yields the coefficient 2a/α. -/
theorem distribution_half_le_of_l1_bound (μ : Measure X) (f : X → ℝ)
    (hf : AEMeasurable f μ) {α a : ℝ} (hα : 0 < α) (M : ℝ≥0∞)
    (hbound : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal a * M) :
    distribution μ f (α / 2) ≤ ENNReal.ofReal (2 * a / α) * M := by
  calc
    _ ≤ (ENNReal.ofReal (α / 2))⁻¹ * ∫⁻ x, ‖f x‖ₑ ∂μ :=
      distribution_le_l1_integral μ f hf (by positivity)
    _ ≤ (ENNReal.ofReal (α / 2))⁻¹ * (ENNReal.ofReal a * M) :=
      mul_le_mul' le_rfl hbound
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < α / 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (α / 2)⁻¹)]
      congr 2
      field_simp

end RothschildStein.H2
