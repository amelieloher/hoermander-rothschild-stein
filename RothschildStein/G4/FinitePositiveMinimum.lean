-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G4

/-- A finite collection of positive radii has a positive common lower
bound, including the empty collection. -/
theorem exists_finite_positive_lower_bound {ι : Type*} (T : Finset ι)
    (c : ι → ℝ) (hc : ∀ i ∈ T, 0 < c i) :
    ∃ a : ℝ, 0 < a ∧ ∀ i ∈ T, a ≤ c i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i T hi ih =>
    obtain ⟨a, ha, hb⟩ := ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    refine ⟨min a (c i), lt_min ha (hc i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hb j hj)

end RothschildStein.G4
