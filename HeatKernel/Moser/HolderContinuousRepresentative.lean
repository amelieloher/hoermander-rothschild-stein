-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderCommonFullMeasureSet
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! Continuous representatives from Hölder control on a full-measure dense set. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory Set
open scoped NNReal
namespace HeatKernel

/-- Hölder control on a dense full-measure set gives a uniformly continuous
representative. The pairwise Hölder estimate is an explicit hypothesis. -/
theorem exists_uniformContinuous_representative_of_holderOnWith
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) {s : Set α} {u : α → ℝ} {C r : ℝ≥0}
    (hs : Dense s) (hfull : ∀ᵐ x ∂μ, x ∈ s)
    (hr : 0 < r) (hu : HolderOnWith C r u s) :
    ∃ v : α → ℝ, UniformContinuous v ∧ EqOn v u s ∧ v =ᵐ[μ] u := by
  have hc : UniformContinuous (fun x : s => u x) :=
    uniformContinuousOn_iff_restrict.mp (hu.uniformContinuousOn hr)
  let v := hs.extend (fun x : s => u x)
  have hv : UniformContinuous v := hs.uniformContinuous_extend hc
  have he : EqOn v u s := by
    intro x hx
    exact hs.extend_of_ind hc ⟨x, hx⟩
  exact ⟨v, hv, he, hfull.mono fun x hx => he hx⟩

end HeatKernel
