-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Constructions

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter Metric
open scoped Topology

namespace RothschildStein.G4

/-- A joint neighborhood contains one spatial ball and one
parameter neighborhood (BB (9.55), p. 453). -/
theorem exists_product_ball_of_eventually {P E : Type*}
    [TopologicalSpace P] [PseudoMetricSpace E] (A : E × P → Prop)
    (x₀ : E) (p₀ : P) (hA : ∀ᶠ q in 𝓝 (x₀, p₀), A q) :
    ∃ r : ℝ, 0 < r ∧ ∃ V : Set P, V ∈ 𝓝 p₀ ∧
      ∀ x ∈ ball x₀ r, ∀ p ∈ V, A (x, p) := by
  rw [nhds_prod_eq] at hA
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hA
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  exact ⟨r, hr, V, hV, fun x hx p hp => hUV ⟨hball hx, hp⟩⟩

end RothschildStein.G4
