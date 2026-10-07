-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingWeightedSpan

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.P1

/-- Every drift-padded word either contains only original
indices (including index zero) or contains an appended diffusion index. -/
theorem padding_drift_word_original_or_added {q d : ℕ}
    (I : List (Fin (q + d + 1))) :
    (∃ L : List (Fin (q + 1)), I = L.map paddingGeneratorIndex) ∨
      ∃ j : Fin d, (Fin.natAdd q j).succ ∈ I := by
  induction I with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons i I ih =>
    rcases ih with ⟨L, hL⟩ | ⟨j, hj⟩
    · subst I
      refine Fin.cases ?_ (fun a => ?_) i
      · exact Or.inl ⟨0 :: L, rfl⟩
      · refine Fin.addCases (fun b => ?_) (fun b => ?_) a
        · exact Or.inl ⟨b.succ :: L, by simp [paddingGeneratorIndex]⟩
        · exact Or.inr ⟨b, List.mem_cons_self⟩
    · exact Or.inr ⟨j, List.mem_cons_of_mem i hj⟩

end RothschildStein.P1
