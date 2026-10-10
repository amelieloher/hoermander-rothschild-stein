-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalizedFormData
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linter

/-! # Localized space-time representatives paired with spatially supported tests -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- Zero extension has no effect on pairings with a spatial test supported in
the extension set. This also applies to any almost-everywhere representative. -/
theorem ae_mul_eq_of_ae_spatial_indicator {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure (α × β)}
    {K : Set β} {F f : α × β → ℝ}
    (hF : F =ᵐ[μ] fun z => K.indicator (fun x => f (z.1, x)) z.2)
    {φ : β → ℝ} (hφ : Function.support φ ⊆ K) :
    (fun z : α × β => F z * φ z.2) =ᵐ[μ] fun z => f z * φ z.2 := by
  filter_upwards [hF] with z hz
  by_cases hmem : z.2 ∈ K
  · simpa only [Set.indicator_of_mem hmem] using congrArg (fun y => y * φ z.2) hz
  · have hzero : φ z.2 = 0 := by
      by_contra h
      exact hmem (hφ h)
    simp only [hzero, mul_zero]

end HeatKernel
