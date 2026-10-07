-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import Mathlib.Data.List.Sublists

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {α κ : Type*}

/-- The explicit recursive kernel/subword pairs of the Friedrichs
commutator induction (BB (2.9)–(2.12), pp. 77–79). This definition records
only the combinatorics; analytic transfer properties are proved separately. -/
def friedrichsCommutatorPairs (base : α → κ) (transfer : α → κ → κ) :
    List α → List (κ × List α)
  | [] => []
  | j :: I =>
      (friedrichsCommutatorPairs base transfer I).map (fun p => (p.1,j :: p.2)) ++
      (friedrichsCommutatorPairs base transfer I).map (fun p => (transfer j p.1,p.2)) ++
      [(base j,I)]

/-- Every recursive pair uses a proper subword of the input word
(BB pp. 77–79). -/
theorem friedrichsCommutatorPairs_subword (base : α → κ) (transfer : α → κ → κ)
    (I : List α) {p : κ × List α} (hp : p ∈ friedrichsCommutatorPairs base transfer I) :
    p.2.Sublist I ∧ p.2.length < I.length := by
  induction I generalizing p with
  | nil => simp [friedrichsCommutatorPairs] at hp
  | cons j I ih =>
    simp only [friedrichsCommutatorPairs,List.mem_append,List.mem_map,List.mem_singleton] at hp
    rcases hp with (⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩) | rfl
    · obtain ⟨hs,hl⟩ := ih ha
      exact ⟨hs.cons_cons j,by simpa only [List.length_cons] using Nat.succ_lt_succ hl⟩
    · obtain ⟨hs,hl⟩ := ih ha
      exact ⟨hs.cons j,by simpa only [List.length_cons] using hl.trans (Nat.lt_succ_self _)⟩
    · exact ⟨List.Sublist.refl I |>.cons j,by simp⟩

end RothschildStein.S
