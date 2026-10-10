-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiEssentialSupremum

/-! # Lower moments on normalized finite-measure sets -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A finite larger moment gives every smaller nonnegative moment on a set of
normalized finite measure. No positive lower bound on the function is needed. -/
theorem lintegral_rpow_ne_top_of_le_exponent {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℝ≥0∞) {U : Set α} (hμU : μ U ≤ 1)
    {p p₀ : ℝ} (hp : 0 ≤ p) (hpp₀ : p ≤ p₀)
    (hmoment : (∫⁻ y in U, f y ^ p₀ ∂μ) ≠ ⊤) :
    (∫⁻ y in U, f y ^ p ∂μ) ≠ ⊤ := by
  have hb : (∫⁻ y in U, f y ^ p ∂μ) ≤ 1 + ∫⁻ y in U, f y ^ p₀ ∂μ := by
    calc
      _ ≤ ∫⁻ y in U, 1 + f y ^ p₀ ∂μ := by
        apply lintegral_mono
        intro y
        by_cases hy : f y ≤ 1
        · exact (ENNReal.rpow_le_one hy hp).trans (le_add_right le_rfl)
        · exact (ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hy) hpp₀).trans
            (le_add_left le_rfl)
      _ = μ U + ∫⁻ y in U, f y ^ p₀ ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          Measure.restrict_apply_univ, one_mul]
      _ ≤ _ := add_le_add hμU le_rfl
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨by simp, hmoment⟩) hb

end HeatKernel
