-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftWeightedSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.P1

/-- A word in the padded alphabet either consists entirely
of original generators or contains an added generator. -/
theorem padding_word_original_or_added {q d : ℕ} (I : List (Fin (q + d))) :
    (∃ L : List (Fin q), I = L.map (Fin.castAdd d)) ∨
      ∃ j : Fin d, Fin.natAdd q j ∈ I := by
  induction I with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons i I ih =>
    rcases ih with ⟨L, hL⟩ | ⟨j, hj⟩
    · subst I
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · exact Or.inl ⟨a :: L, rfl⟩
      · exact Or.inr ⟨b, List.mem_cons_self⟩
    · exact Or.inr ⟨j, List.mem_cons_of_mem i hj⟩

end RothschildStein.P1
