-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
import Mathlib.Tactic.Linter

/-! # Evaluation of measurable families of continuous maps -/

@[expose] public section

open MeasureTheory

namespace HeatKernel

/-- Pointwise almost everywhere strong measurability of a continuous family implies strong
measurability when the argument itself varies measurably. -/
theorem aestronglyMeasurable_apply_of_continuous {T E F : Type*}
    [MeasurableSpace T] {μ : Measure T}
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    {A : T → E → F} (hA : ∀ t, Continuous (A t))
    (hAm : ∀ e, AEStronglyMeasurable (fun t => A t e) μ)
    {v : T → E} (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun t => A t (v t)) μ := by
  have H := measurable_uncurry_of_continuous_of_measurable
    (α := NullMeasurableSpace T μ) (u := fun e t => A t e) hA
    (fun e => (hAm e).aemeasurable.nullMeasurable.measurable')
  have hv' := hv.aemeasurable.nullMeasurable.measurable'
  have hn : NullMeasurable (fun t => A t (v t)) μ := by
    change @Measurable (NullMeasurableSpace T μ) F _ _ _
    exact H.comp (hv'.prodMk measurable_id)
  exact hn.aemeasurable.aestronglyMeasurable



end HeatKernel
