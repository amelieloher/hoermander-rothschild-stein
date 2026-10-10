-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Tactic.Linter

/-! # Essential extrema of stationary functions

A nonzero time factor does not change almost everywhere spatial predicates, or the
extended nonnegative essential extrema of a function constant in time.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace HeatKernel

/-- Almost everywhere spatial predicates are equivalent to the corresponding stationary
predicates on a product with a nonzero first measure. -/
theorem ae_snd_iff_of_measure_ne_zero {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] (hμ : μ ≠ 0) {p : β → Prop} :
    (∀ᵐ z ∂μ.prod ν, p z.2) ↔ ∀ᵐ y ∂ν, p y := by
  constructor
  · intro h
    have : (ae μ).NeBot := ae_neBot.mpr hμ
    obtain ⟨_, hx⟩ := (Measure.ae_ae_of_ae_prod h).exists
    exact hx
  · intro h
    exact (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae h

/-- The essential supremum of a stationary nonnegative extended real function is unchanged
by taking a product with a nonzero time measure. -/
theorem essSup_snd_eq_of_measure_ne_zero {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] (hμ : μ ≠ 0) (f : β → ℝ≥0∞) :
    essSup (fun z : α × β => f z.2) (μ.prod ν) = essSup f ν := by
  apply le_antisymm
  · refine essSup_le_of_ae_le _ ?_ (by isBoundedDefault)
    exact (ae_snd_iff_of_measure_ne_zero hμ).mpr (ae_le_essSup)
  · refine essSup_le_of_ae_le _ ?_ (by isBoundedDefault)
    exact (ae_snd_iff_of_measure_ne_zero hμ).mp (ae_le_essSup)

/-- The essential infimum of a stationary nonnegative extended real function is unchanged
by taking a product with a nonzero time measure. -/
theorem essInf_snd_eq_of_measure_ne_zero {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] (hμ : μ ≠ 0) (f : β → ℝ≥0∞) :
    essInf (fun z : α × β => f z.2) (μ.prod ν) = essInf f ν := by
  apply le_antisymm
  · refine le_essInf_of_ae_le _ ?_ (by isBoundedDefault)
    exact (ae_snd_iff_of_measure_ne_zero hμ).mp (ae_essInf_le)
  · refine le_essInf_of_ae_le _ ?_ (by isBoundedDefault)
    exact (ae_snd_iff_of_measure_ne_zero hμ).mpr (ae_essInf_le)

end HeatKernel
