-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiReverseHolderFamily

/-! # Normalization by a positive finite reference-set measure -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Rescaling by the reference-set measure, without restricting the underlying domain. -/
def normalizedReferenceMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (V : Set α) : Measure α := (μ V)⁻¹ • μ

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : Set α}

/-- Every set measure has the same reference normalization. -/
theorem normalizedReferenceMeasure_apply (s : Set α) :
    normalizedReferenceMeasure μ V s = (μ V)⁻¹ * μ s := by
  rw [normalizedReferenceMeasure, Measure.smul_apply, smul_eq_mul]

/-- The positive finite reference set has normalized measure one. -/
theorem normalizedReferenceMeasure_reference (hzero : μ V ≠ 0) (hfinite : μ V ≠ ⊤) :
    normalizedReferenceMeasure μ V V = 1 := by
  rw [normalizedReferenceMeasure_apply, ENNReal.inv_mul_cancel hzero hfinite]

/-- Multiplication by the nonzero normalization scalar preserves restricted
essential suprema, including on sets other than the reference set. -/
theorem essSup_normalizedReferenceMeasure_restrict (hfinite : μ V ≠ ⊤)
    (f : α → ℝ≥0∞) (U : Set α) :
    essSup f ((normalizedReferenceMeasure μ V).restrict U) = essSup f (μ.restrict U) := by
  have hc : (μ V)⁻¹ ≠ 0 := by simp [hfinite]
  rw [normalizedReferenceMeasure, Measure.restrict_smul]
  simp only [essSup, Measure.ae_ennreal_smul_measure_eq hc]

/-- Restricted moments acquire the single inverse reference-measure factor. -/
theorem lintegral_normalizedReferenceMeasure_restrict (f : α → ℝ≥0∞) (U : Set α) :
    (∫⁻ y in U, f y ∂normalizedReferenceMeasure μ V) = (μ V)⁻¹ * ∫⁻ y in U, f y ∂μ := by
  rw [normalizedReferenceMeasure, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

/-- A finite moment remains finite when the reference measure is positive. -/
theorem lintegral_normalizedReferenceMeasure_ne_top (hzero : μ V ≠ 0)
    (f : α → ℝ≥0∞) (U : Set α) (hf : (∫⁻ y in U, f y ∂μ) ≠ ⊤) :
    (∫⁻ y in U, f y ∂normalizedReferenceMeasure μ V) ≠ ⊤ := by
  rw [lintegral_normalizedReferenceMeasure_restrict]
  exact ENNReal.mul_ne_top (by simp [hzero]) hf

/-- A relative reference-measure tail bound becomes its normalized bound. -/
theorem normalizedReferenceMeasure_le_of_relative_bound
    (hzero : μ V ≠ 0) (hfinite : μ V ≠ ⊤) {s : Set α} {B : ℝ≥0∞}
    (hb : μ s ≤ B * μ V) : normalizedReferenceMeasure μ V s ≤ B := by
  rw [normalizedReferenceMeasure_apply]
  calc
    (μ V)⁻¹ * μ s ≤ (μ V)⁻¹ * (B * μ V) := mul_le_mul' le_rfl hb
    _ = B * ((μ V)⁻¹ * μ V) := by ac_rfl
    _ = B := by rw [ENNReal.inv_mul_cancel hzero hfinite, mul_one]

end HeatKernel
