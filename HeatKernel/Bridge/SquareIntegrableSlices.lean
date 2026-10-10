-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linter

/-! # Square-integrable spatial slices of functions on product measure spaces -/

@[expose] public section
open MeasureTheory
namespace HeatKernel

/-- A square-integrable function on a product has square-integrable spatial slices
at almost every time. -/
theorem ae_memLp_two_slice {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ t ∂μ, MemLp (fun x => f (t, x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
    with t hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

/-- Square integrability on a rectangle gives square-integrable spatial
slices with the corresponding restricted spatial measure. -/
theorem ae_memLp_two_slice_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {J : Set α} {K : Set β}
    {f : α × β → ℝ} (hf : MemLp f 2 ((μ.prod ν).restrict (J ×ˢ K))) :
    ∀ᵐ t ∂(μ.restrict J), MemLp (fun x => f (t, x)) 2 (ν.restrict K) := by
  apply ae_memLp_two_slice
  simpa only [Measure.prod_restrict J K] using hf

end HeatKernel
