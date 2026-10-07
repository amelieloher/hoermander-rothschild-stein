-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FiniteDescentChain
public import RothschildStein.G4.FiniteClosedCoverStep
public import Mathlib.Data.Option.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A finite closed interval cover has a decreasing overlap
chain from the reference interval to an interval containing the target,
without repetition and within the finite cardinality bound
(BB (9.57), p. 454). -/
theorem exists_decreasing_interval_overlap_chain {ι : Type*} [Fintype ι]
    (S : ι → Set ℝ) {r R : ℝ}
    (hS : ∀ B, IsClosed (S B)) (hbound : ∀ B, S B ⊆ Icc r R)
    (hcover : Icc r R ⊆ ⋃ B, S B) (B₀ : ι) (hstart : R ∈ S B₀) :
    ∃ l : List ι,
      l.IsChain (fun B C => sInf (S B) ∈ S C ∧ sInf (S C) < sInf (S B)) ∧
      l.Pairwise (fun B C => sInf (S C) < sInf (S B)) ∧
      l.head? = some B₀ ∧ (∀ C ∈ l.getLast?, r ∈ S C) ∧
      (∀ C ∈ l, (S C).Nonempty) ∧ l.Nodup ∧ l.length ≤ Fintype.card ι := by
  classical
  let V := {B : ι // (S B).Nonempty}
  let nonemptyIntervalIndexFintype : Fintype V := Fintype.ofFinite V
  let level : V → ℝ := fun B => sInf (S B.val)
  let edge : V → V → Prop := fun B C => level B ∈ S C.val ∧ level C < level B
  let terminal : V → Prop := fun B => r ∈ S B.val
  have hnext : ∀ B : V, ¬ terminal B → ∃ C : V, edge B C ∧ level C < level B := by
    intro B hnot
    obtain ⟨hmem, hrle, hleast⟩ :=
      closed_radius_interval_left_endpoint (hS B.val) B.property (hbound B.val)
    have hneq : sInf (S B.val) ≠ r := by
      intro heq
      apply hnot
      change r ∈ S B.val
      rwa [← heq]
    have hra : r < level B := lt_of_le_of_ne hrle hneq.symm
    have haR : level B ≤ R := (hbound B.val hmem).2
    obtain ⟨C, hBC, z, hz, hza⟩ := finite_closed_cover_has_left_overlap S hS hcover hra haR
    have hCne : (S C).Nonempty := ⟨z, hz⟩
    have hlt : sInf (S C) < level B :=
      ((closed_radius_interval_left_endpoint (hS C) hCne (hbound C)).2.2 z hz).trans_lt hza
    exact ⟨⟨C, hCne⟩, ⟨hBC, hlt⟩, hlt⟩
  let start : V := ⟨B₀, ⟨R, hstart⟩⟩
  obtain ⟨l, hchain, hpair, hhead, hterm, hnodup, hlength⟩ :=
    exists_finite_descending_terminal_chain level edge terminal hnext start
  refine ⟨l.map Subtype.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (List.isChain_map Subtype.val).mpr hchain
  · exact List.pairwise_map.mpr hpair
  · simp only [List.head?_map, hhead, Option.map_some]
    rfl
  · intro C hC
    rw [List.getLast?_map] at hC
    obtain ⟨D, hD, hDC⟩ := Option.mem_map.mp hC
    exact hDC ▸ hterm D hD
  · intro C hC
    obtain ⟨D, _, hDC⟩ := List.mem_map.mp hC
    exact hDC ▸ D.property
  · exact hnodup.map Subtype.val_injective
  · rw [List.length_map]
    exact hlength.trans (Fintype.card_le_of_injective (Subtype.val : V → ι) Subtype.val_injective)

end RothschildStein.G4
