-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionIntervals
public import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Tactic.Linter

/-! # Uniform estimates on cylinders touching an open top time -/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Almost-everywhere bounds on all time-truncated cylinders hold on the full open-top cylinder. -/
theorem ae_le_on_prod_Ioo_of_interiorTopTime_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure (ℝ × E)) (a b : ℝ) (B : Set E) {f : ℝ × E → ℝ≥0∞} {C : ℝ≥0∞}
    (hbound : ∀ n, ∀ᵐ z ∂μ.restrict ((Ioo a (interiorTopTime b n)) ×ˢ B), f z ≤ C) :
    ∀ᵐ z ∂μ.restrict ((Ioo a b) ×ˢ B), f z ≤ C := by
  rw [← iUnion_prod_Ioo_interiorTopTime a b B]
  exact (ae_restrict_iUnion_iff _ _).mpr hbound

/-- A uniform essential supremum bound survives exhaustion toward an open top time. -/
theorem essSup_prod_Ioo_le_of_interiorTopTime_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure (ℝ × E)) (a b : ℝ) (B : Set E) (f : ℝ × E → ℝ≥0∞) {C : ℝ≥0∞}
    (hbound : ∀ n, essSup f (μ.restrict ((Ioo a (interiorTopTime b n)) ×ˢ B)) ≤ C) :
    essSup f (μ.restrict ((Ioo a b) ×ˢ B)) ≤ C := by
  exact essSup_le_of_ae_le C
    (ae_le_on_prod_Ioo_of_interiorTopTime_bounds μ a b B
      (fun n => (ENNReal.ae_le_essSup f).mono fun z hz => hz.trans (hbound n)))

end HeatKernel
