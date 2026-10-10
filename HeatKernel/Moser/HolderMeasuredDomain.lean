-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderCommonFullMeasureSet
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic

/-! # Essential oscillations on measured open domains -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace HeatKernel

/-- Pullback along a measurable embedding preserves almost-everywhere assertions. -/
theorem ae_comap_of_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {e : A → B} (he : MeasurableEmbedding e) {μ : Measure B} {p : B → Prop}
    (hp : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂μ.comap e, p (e x) := by
  apply he.ae_map_iff.mp
  rw [he.map_comap]
  exact ae_restrict_of_ae hp

/-- Essential bounds pull back to a measured subdomain. -/
theorem boundedUnder_comap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {e : A → B} (he : MeasurableEmbedding e) {μ : Measure B} {u : B → ℝ}
    (hup : IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hlo : IsBoundedUnder (· ≥ ·) (ae μ) u) :
    IsBoundedUnder (· ≤ ·) (ae (μ.comap e)) (u ∘ e) ∧
      IsBoundedUnder (· ≥ ·) (ae (μ.comap e)) (u ∘ e) := by
  obtain ⟨M, hM⟩ := hup
  obtain ⟨m, hm⟩ := hlo
  exact ⟨⟨M, ae_comap_of_ae he hM⟩, ⟨m, ae_comap_of_ae he hm⟩⟩

/-- The real essential oscillation of the zero measure is zero. -/
theorem essential_oscillation_zero {A : Type*} [MeasurableSpace A] (u : A → ℝ) :
    essSup u (0 : Measure A) - essInf u (0 : Measure A) = 0 := by
  simp [essSup, essInf, Filter.limsup, Filter.liminf, Filter.limsSup, Filter.limsInf]

/-- A bounded real function has nonnegative essential oscillation. -/
theorem essential_oscillation_nonneg {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {u : A → ℝ}
    (hup : IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hlo : IsBoundedUnder (· ≥ ·) (ae μ) u) :
    0 ≤ essSup u μ - essInf u μ := by
  by_cases hμ : μ = 0
  · rw [hμ, essential_oscillation_zero]
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  obtain ⟨x, hx⟩ := ((ae_essInf_le hlo).and (ae_le_essSup hup)).exists
  exact sub_nonneg.mpr (hx.1.trans hx.2)

/-- Essential oscillation is monotone under restriction, including empty sets. -/
theorem essential_oscillation_mono {A : Type*} [MeasurableSpace A]
    {μ ν : Measure A} {u : A → ℝ} (hν : ν ≤ μ)
    (hup : IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hlo : IsBoundedUnder (· ≥ ·) (ae μ) u) :
    essSup u ν - essInf u ν ≤ essSup u μ - essInf u μ := by
  by_cases hz : ν = 0
  · rw [hz, essential_oscillation_zero]
    exact essential_oscillation_nonneg hup hlo
  exact essential_oscillation_le_of_measure_le hz hν hup hlo

/-- Passing to a measured subdomain cannot increase a finite essential oscillation. -/
theorem essential_oscillation_comap_le {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {e : A → B}
    (he : MeasurableEmbedding e) {μ : Measure B} {u : B → ℝ}
    (hup : IsBoundedUnder (· ≤ ·) (ae μ) u)
    (hlo : IsBoundedUnder (· ≥ ·) (ae μ) u) :
    essSup (u ∘ e) (μ.comap e) - essInf (u ∘ e) (μ.comap e) ≤
      essSup u μ - essInf u μ := by
  by_cases hz : μ.comap e = 0
  · rw [hz, essential_oscillation_zero]
    exact essential_oscillation_nonneg hup hlo
  have : (ae (μ.comap e)).NeBot := ae_neBot.mpr hz
  obtain ⟨hup', hlo'⟩ := boundedUnder_comap he hup hlo
  exact sub_le_sub
    (essSup_le_of_ae_le _ (ae_comap_of_ae he (ae_le_essSup hup))
      hlo'.isCoboundedUnder_le)
    (le_essInf_of_ae_le _ (ae_comap_of_ae he (ae_essInf_le hlo))
      hup'.isCoboundedUnder_ge)

/-- A continuous representative on an embedded domain extends to the ambient
space, with continuity and almost-everywhere equality on the image. -/
theorem exists_representative_on_embedding_range {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace A] [MeasurableSpace B]
    {e : A → B} (he : Topology.IsEmbedding e) (hme : MeasurableEmbedding e)
    (μ : Measure B) (u : B → ℝ) (v : A → ℝ) (hv : Continuous v)
    (heq : v =ᵐ[μ.comap e] u ∘ e) :
    ∃ w : B → ℝ, ContinuousOn w (range e) ∧
      w =ᵐ[μ.restrict (range e)] u ∧ ∀ x, w (e x) = v x := by
  let w : B → ℝ := Function.extend e v (fun _ => 0)
  have hw (x : A) : w (e x) = v x := he.injective.extend_apply _ _ x
  refine ⟨w, ?_, ?_, hw⟩
  · rw [← image_univ, he.isInducing.continuousOn_image_iff]
    simpa only [Function.comp_def, hw] using hv.continuousOn
  · rw [← hme.map_comap]
    change ∀ᵐ x ∂Measure.map e (μ.comap e), w x = u x
    rw [hme.ae_map_iff]
    exact heq.mono fun x hx => (hw x).trans hx

end HeatKernel
