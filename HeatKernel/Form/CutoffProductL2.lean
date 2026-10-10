-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalWeakCutoffs
public import HeatKernel.Moser.JointMeasurability
import Mathlib.Tactic.Linter

/-! # Product square integrability of interior spatial cutoffs -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- A product function vanishing outside a spatial set is globally Lp when its restriction is. -/
theorem memLp_prod_of_restrict_of_zero_outside {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {s : Set β} (hs : MeasurableSet s)
    {f : α × β → E} {p : ℝ≥0∞} (hf : MemLp f p (μ.prod (ν.restrict s)))
    (hz : ∀ z : α × β, z.2 ∉ s → f z = 0) : MemLp f p (μ.prod ν) := by
  have hr : MemLp f p ((μ.prod ν).restrict (univ ×ˢ s)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    exact hf
  have hi := (memLp_indicator_iff_restrict ((MeasurableSet.univ : MeasurableSet (univ : Set α)).prod hs)).mpr hr
  have he : (univ ×ˢ s).indicator f = f := by
    funext z
    by_cases h : z.2 ∈ s
    · exact indicator_of_mem (show z ∈ (univ : Set α) ×ˢ s from ⟨mem_univ _, h⟩) f
    · rw [indicator_of_notMem (fun ht => h ht.2), hz z h]
  exact he ▸ hi

/-- Multiplication by a smooth compact spatial cutoff turns local product L² data into global
spatial product L² data. -/
theorem memLp_product_mul_smooth_compact {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {N : ℕ} (U : Opens (Fin N → ℝ))
    {f : α → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    MemLp (fun z : α × (Fin N → ℝ) => f z.1 z.2 * φ z.2) 2 (μ.prod volume) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  apply memLp_prod_of_restrict_of_zero_outside U.isOpen.measurableSet
  · have hm : AEStronglyMeasurable (fun z : α × (Fin N → ℝ) => φ z.2)
        (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))) :=
      (hφ.continuous.stronglyMeasurable.comp_measurable measurable_snd).aestronglyMeasurable
    simpa only [mul_comm, Function.uncurry_def] using memLp_two_mul_of_ae_bound hm hf
      (Filter.Eventually.of_forall fun z => hC z.2)
  · intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht)), mul_zero]


end HeatKernel
