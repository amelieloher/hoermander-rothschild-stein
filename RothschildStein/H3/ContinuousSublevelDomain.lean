-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic
public import Mathlib.Topology.Sets.Opens

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace
variable {X : Type*} [TopologicalSpace X]

/-- Open sublevels of a continuous gauge, without a metric requirement. -/
def continuousSublevelDomain (ν : X → ℝ) (hν : Continuous ν) (R : ℝ) : Opens X :=
  ⟨{x | ν x < R}, isOpen_lt hν continuous_const⟩

/-- Every compact set fits in one positive-radius gauge sublevel. -/
theorem continuousSublevelDomain_compact_cofinal (ν : X → ℝ) (hν : Continuous ν)
    {K : Set X} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ (continuousSublevelDomain ν hν R : Set X) := by
  obtain ⟨a, ha⟩ := hK.bddAbove_image hν.continuousOn
  refine ⟨max 0 a + 1, by positivity, ?_⟩
  intro x hx
  have hh : ν x ≤ a := ha (mem_image_of_mem ν hx)
  change ν x < max 0 a + 1
  linarith [le_max_right (0 : ℝ) a]

end RothschildStein.H3
