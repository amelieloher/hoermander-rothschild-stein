-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Basic.Real.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- Finitely many positive reference radii have a positive
common lower bound, also chosen at most one (BB pp. 453–454). -/
theorem exists_positive_finset_reference_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ i ∈ s, b ≤ f i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | @insert i s hi ih =>
      intro hf
      obtain ⟨b, hb, hb1, hbf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      refine ⟨min b (f i), lt_min hb (hf i (Finset.mem_insert_self _ _)),
        (min_le_left _ _).trans hb1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbf j hj)

end RothschildStein.G4
