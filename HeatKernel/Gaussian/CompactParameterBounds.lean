-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic

/-! # Local uniform bounds on compact parameter families

Joint continuity near a parameter and compactness of the integration variables
give one norm bound valid on a common parameter neighborhood.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Metric
namespace HeatKernel.Gaussian

/-- Joint continuity on an open parameter region gives a uniform bound on a
common parameter ball and a compact set of integration variables. -/
theorem exists_local_uniform_bound_on_compact {E Z F : Type*}
    [PseudoMetricSpace E] [ProperSpace E] [TopologicalSpace Z] [NormedAddCommGroup F]
    {U : Set E} (hU : IsOpen U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {K : Set Z} (hK : IsCompact K) {f : E × Z → F}
    (hf : ContinuousOn f (U ×ˢ univ)) :
    ∃ ε B : ℝ, 0 < ε ∧ 0 ≤ B ∧ ball x₀ ε ⊆ U ∧
      ∀ x ∈ ball x₀ ε, ∀ z ∈ K, ‖f (x, z)‖ ≤ B := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  have hsub : closedBall x₀ (δ / 2) ⊆ U := by
    intro x hx
    apply hball
    change dist x x₀ < δ
    have H := mem_closedBall.mp hx
    linarith
  have hc : IsCompact (closedBall x₀ (δ / 2) ×ˢ K) := (isCompact_closedBall x₀ (δ / 2)).prod hK
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn
    (hf.mono (fun z hz ↦ ⟨hsub hz.1, mem_univ z.2⟩))
  refine ⟨δ / 2, max B 0, by positivity, le_max_right _ _,
    ball_subset_closedBall.trans hsub, ?_⟩
  intro x hx z hz
  exact (hB (x, z) ⟨ball_subset_closedBall hx, hz⟩).trans (le_max_left _ _)

end HeatKernel.Gaussian
