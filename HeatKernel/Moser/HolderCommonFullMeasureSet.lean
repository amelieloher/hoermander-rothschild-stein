-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith

/-! Simultaneous pointwise essential bounds on a countable family of cylinders. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory Set Filter
namespace HeatKernel

/-- Restricting a nonzero measure cannot increase the essential oscillation
of an essentially bounded real function. -/
theorem essential_oscillation_le_of_measure_le
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {u : α → ℝ}
    (hν : ν ≠ 0) (hsub : ν ≤ μ)
    (hupper : IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hlower : IsBoundedUnder (· ≥ ·) (ae μ) u) :
    essSup u ν - essInf u ν ≤ essSup u μ - essInf u μ := by
  have : (ae ν).NeBot := ae_neBot.mpr hν
  have hup := IsBoundedUnder.mono (ae_mono hsub) hupper
  have hlo := IsBoundedUnder.mono (ae_mono hsub) hlower
  exact sub_le_sub
    (essSup_mono_measure' hsub hlo.isCoboundedUnder_le hupper)
    (essInf_antitone_measure hsub.absolutelyContinuous hlower hup.isCoboundedUnder_ge)

/-- Removing the exceptional sets for countably many cylinders gives one dense
full-measure set on which every essential oscillation controls pairs of values.
Positivity on open sets supplies density without a differentiation theorem. -/
theorem exists_dense_full_measure_set_essential_oscillation
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [μ.IsOpenPosMeasure] (C : ι → Set α) (u : α → ℝ)
    (hupper : ∀ i, IsBoundedUnder (· ≤ ·) (ae (μ.restrict (C i))) u)
    (hlower : ∀ i, IsBoundedUnder (· ≥ ·) (ae (μ.restrict (C i))) u) :
    ∃ s : Set α, (∀ᵐ x ∂μ, x ∈ s) ∧ Dense s ∧
      ∀ i x, x ∈ s → x ∈ C i →
        essInf u (μ.restrict (C i)) ≤ u x ∧ u x ≤ essSup u (μ.restrict (C i)) := by
  let s : Set α := {x | ∀ i, x ∈ C i →
    essInf u (μ.restrict (C i)) ≤ u x ∧ u x ≤ essSup u (μ.restrict (C i))}
  have hs : ∀ᵐ x ∂μ, x ∈ s := by
    apply ae_all_iff.mpr
    intro i
    exact ae_imp_of_ae_restrict ((ae_essInf_le (hlower i)).and (ae_le_essSup (hupper i)))
  exact ⟨s, hs, μ.dense_of_ae hs, fun _ _ hx => hx _⟩

/-- On one dense full-measure set, the essential oscillation on every member
of a countable family bounds all pairs of values in that member. -/
theorem exists_dense_full_measure_set_pair_oscillation
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [μ.IsOpenPosMeasure] (C : ι → Set α) (u : α → ℝ)
    (hupper : ∀ i, IsBoundedUnder (· ≤ ·) (ae (μ.restrict (C i))) u)
    (hlower : ∀ i, IsBoundedUnder (· ≥ ·) (ae (μ.restrict (C i))) u) :
    ∃ s : Set α, (∀ᵐ x ∂μ, x ∈ s) ∧ Dense s ∧
      ∀ i x y, x ∈ s → y ∈ s → x ∈ C i → y ∈ C i →
        |u x - u y| ≤ essSup u (μ.restrict (C i)) - essInf u (μ.restrict (C i)) := by
  obtain ⟨s, hs, hd, hbounds⟩ :=
    exists_dense_full_measure_set_essential_oscillation μ C u hupper hlower
  refine ⟨s, hs, hd, ?_⟩
  intro i x y hx hy hxi hyi
  obtain ⟨hxl, hxu⟩ := hbounds i x hx hxi
  obtain ⟨hyl, hyu⟩ := hbounds i y hy hyi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end HeatKernel
