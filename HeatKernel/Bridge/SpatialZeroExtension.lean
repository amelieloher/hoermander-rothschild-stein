-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linter

/-! # Extending spatially localized space-time data by zero -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- A function square integrable on a spatially restricted product remains square
integrable after zero extension to the whole spatial measure. -/
theorem memLp_two_spatial_zero_extension {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {K : Set β} (hK : MeasurableSet K) {f : α × β → ℝ}
    (hf : MemLp f 2 (μ.prod (ν.restrict K))) :
    MemLp (fun z : α × β => K.indicator (fun x => f (z.1, x)) z.2) 2 (μ.prod ν) := by
  have hf' : MemLp f 2 ((μ.prod ν).restrict (univ ×ˢ K)) := by
    rw [← Measure.prod_restrict (univ : Set α) K, Measure.restrict_univ]
    exact hf
  have hS : MeasurableSet ((univ : Set α) ×ˢ K) := MeasurableSet.univ.prod hK
  have hi := (memLp_indicator_iff_restrict hS).mpr hf'
  have heq : ((univ : Set α) ×ˢ K).indicator f =
      (fun z : α × β => K.indicator (fun x => f (z.1, x)) z.2) := by
    funext z
    by_cases hz : z.2 ∈ K
    · rw [Set.indicator_of_mem (show z ∈ (univ : Set α) ×ˢ K from ⟨mem_univ _, hz⟩),
        Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem (show z ∉ (univ : Set α) ×ˢ K from fun h => hz h.2),
        Set.indicator_of_notMem hz]
  rw [← heq]
  exact hi

end HeatKernel
