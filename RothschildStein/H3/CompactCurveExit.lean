-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.H3
variable {X : Type*} [MetricSpace X]

/-- A continuous curve from a compact subset of an open set
to its exterior passes through the open set outside that compact subset.
A compact thickening and the intermediate value theorem supply the point. -/
theorem exists_curve_point_outside_compact {K A : Set X}
    (hK : IsCompact K) (hA : IsOpen A) (hKA : K ⊆ A)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1))
    (h0 : γ 0 ∈ K) (h1 : γ 1 ∉ A) :
    ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ A ∧ γ t ∉ K := by
  obtain ⟨ε, hε, hbuffer⟩ := hK.exists_cthickening_subset_open hA hKA
  have hfar : ENNReal.ofReal ε < infEDist (γ 1) K := by
    apply lt_of_not_ge
    intro h
    exact h1 (hbuffer (mem_cthickening_iff.mpr h))
  have hnear : infEDist (γ 0) K = 0 := infEDist_zero_of_mem h0
  have hc : ContinuousOn (fun t => infEDist (γ t) K) (Icc (0 : ℝ) 1) :=
    continuous_infEDist.comp_continuousOn hγ
  have htarget : ENNReal.ofReal (ε / 2) ∈
      Icc (infEDist (γ 0) K) (infEDist (γ 1) K) := by
    rw [hnear]
    exact ⟨bot_le, (ENNReal.ofReal_le_ofReal (by linarith : ε / 2 ≤ ε)).trans hfar.le⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc htarget
  change infEDist (γ t) K = ENNReal.ofReal (ε / 2) at he
  refine ⟨t, ht, hbuffer (mem_cthickening_iff.mpr ?_), ?_⟩
  · rw [he]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro hmem
    have hz := infEDist_zero_of_mem hmem
    rw [hz] at he
    exact (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε / 2)).ne' he.symm

end RothschildStein.H3
