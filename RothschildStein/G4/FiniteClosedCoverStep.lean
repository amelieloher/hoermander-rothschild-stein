-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Before the target radius, a finite closed cover has an
interval containing the current endpoint and some point strictly to its
left. This gives the strictly decreasing transition (BB (9.57), p. 454). -/
theorem finite_closed_cover_has_left_overlap {ι : Type*} [Fintype ι]
    (S : ι → Set ℝ) (hS : ∀ i, IsClosed (S i)) {r R a : ℝ}
    (hcover : Icc r R ⊆ ⋃ i, S i) (hra : r < a) (haR : a ≤ R) :
    ∃ i, a ∈ S i ∧ ∃ z ∈ S i, z < a := by
  have hsub : Ico r a ⊆ ⋃ i, S i ∩ Iio a := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hz.1, hz.2.le.trans haR⟩)
    exact mem_iUnion.mpr ⟨i, hi, hz.2⟩
  have hmem : a ∈ closure (Ico r a) := by
    rw [closure_Ico hra.ne]
    exact ⟨hra.le, le_rfl⟩
  have hmem' := closure_mono hsub hmem
  rw [closure_iUnion_of_finite] at hmem'
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem'
  have hai : a ∈ S i := by
    have hh := closure_mono inter_subset_left hi
    rwa [(hS i).closure_eq] at hh
  obtain ⟨z, hz, hza⟩ := (show (closure (S i ∩ Iio a)).Nonempty from ⟨a, hi⟩).of_closure
  exact ⟨i, hai, z, hz, hza⟩

/-- A nonempty closed interval restricted to a bounded radius
range contains its own left endpoint (BB (9.57), p. 454). -/
theorem closed_radius_interval_left_endpoint {S : Set ℝ} {r R : ℝ}
    (hS : IsClosed S) (hne : S.Nonempty) (hsub : S ⊆ Icc r R) :
    sInf S ∈ S ∧ r ≤ sInf S ∧ ∀ z ∈ S, sInf S ≤ z := by
  have hbound : BddBelow S := ⟨r, fun z hz => (hsub hz).1⟩
  exact ⟨hS.csInf_mem hne hbound, le_csInf hne (fun z hz => (hsub hz).1),
    fun z hz => csInf_le hbound hz⟩

end RothschildStein.G4
