-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BoundedIntervalOverlapChain
public import Mathlib.Data.List.Nodup

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The decreasing overlap chain can end at the requested
interval. A final switch at the target radius is allowed; all other
endpoint transitions are strict, and no index repeats
(BB (9.57), p. 454). -/
theorem exists_requested_interval_overlap_chain {ι : Type*} [Fintype ι]
    (S : ι → Set ℝ) {r R : ℝ}
    (hS : ∀ B, IsClosed (S B)) (hbound : ∀ B, S B ⊆ Icc r R)
    (hcover : Icc r R ⊆ ⋃ B, S B) (B₀ Btarget : ι)
    (hstart : R ∈ S B₀) (htarget : r ∈ S Btarget) :
    ∃ l : List ι,
      l.IsChain (fun B C => sInf (S B) ∈ S C ∧
        (C ≠ Btarget → sInf (S C) < sInf (S B))) ∧
      l.head? = some B₀ ∧ l.getLast? = some Btarget ∧
      (∀ C ∈ l, (S C).Nonempty) ∧ l.Nodup ∧ l.length ≤ Fintype.card ι := by
  classical
  obtain ⟨l, hchain, _hpair, hhead, hterm, hmembers, hnodup, _hlen⟩ :=
    exists_decreasing_interval_overlap_chain S hS hbound hcover B₀ hstart
  let edge := fun B C => sInf (S B) ∈ S C ∧
    (C ≠ Btarget → sInf (S C) < sInf (S B))
  have hweak : l.IsChain edge := hchain.imp (fun {_ _} h => ⟨h.1, fun _ => h.2⟩)
  by_cases hBt : Btarget ∈ l
  · obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp hBt
    have hwhole : ((p ++ [Btarget]) ++ q).IsChain edge := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hweak
    have hnwhole : ((p ++ [Btarget]) ++ q).Nodup := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hnodup
    have hnpre := hnwhole.of_append_left
    refine ⟨p ++ [Btarget], hwhole.left_of_append, ?_, by simp, ?_, hnpre, hnpre.length_le_card⟩
    · simpa only [List.head?_append, List.head?_cons] using hhead
    · intro C hC
      apply hmembers C
      rcases List.mem_append.mp hC with hC | hC
      · exact List.mem_append.mpr (Or.inl hC)
      · have heq : C = Btarget := by simpa using hC
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq)))
  · have hne : l ≠ [] := by intro heq; simp [heq] at hhead
    have hnnew : (l ++ [Btarget]).Nodup :=
      hnodup.append (List.nodup_singleton _) (List.disjoint_singleton.mpr hBt)
    refine ⟨l ++ [Btarget], ?_, ?_, by simp, ?_, hnnew, hnnew.length_le_card⟩
    · apply hweak.append (List.isChain_singleton _)
      intro C hC D hD
      have hDB : D = Btarget := (show Btarget = D from by simpa using hD).symm
      subst D
      have hCne := hmembers C (List.mem_of_mem_getLast? hC)
      have hendpoint := closed_radius_interval_left_endpoint (hS C) hCne (hbound C)
      have heq : sInf (S C) = r :=
        le_antisymm (hendpoint.2.2 r (hterm C hC)) hendpoint.2.1
      refine ⟨?_, fun h => (h rfl).elim⟩
      rwa [heq]
    · simpa only [List.head?_append_of_ne_nil l hne] using hhead
    · intro C hC
      rcases List.mem_append.mp hC with hC | hC
      · exact hmembers C hC
      · have heq : C = Btarget := by simpa using hC
        exact heq.symm ▸ (show (S Btarget).Nonempty from ⟨r, htarget⟩)

end RothschildStein.G4
