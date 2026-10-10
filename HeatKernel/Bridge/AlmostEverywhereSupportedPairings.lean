-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalizedDataPairings
import Mathlib.Tactic.Linter

/-! # Spatial zero extensions paired with almost everywhere supported functions -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- A spatial zero extension can be removed when the test vanishes almost everywhere
outside the extension set. -/
theorem ae_mul_eq_of_ae_spatial_indicator_of_ae_zero {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite ν]
    {K : Set β} {F f : α × β → ℝ}
    (hF : F =ᵐ[μ.prod ν] fun z => K.indicator (fun x => f (z.1, x)) z.2)
    {φ : β → ℝ} (hφ : ∀ᵐ x ∂ν, x ∉ K → φ x = 0) :
    (fun z : α × β => F z * φ z.2) =ᵐ[μ.prod ν] fun z => f z * φ z.2 := by
  have hp := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν) |>.ae hφ
  filter_upwards [hF, hp] with z hz hzero
  by_cases hmem : z.2 ∈ K
  · simpa only [Set.indicator_of_mem hmem] using congrArg (fun y => y * φ z.2) hz
  · simp only [hzero hmem, mul_zero]

end HeatKernel
