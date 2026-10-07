-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakWordWeightCases
public import RothschildStein.H3.WeakHorizontalNorms

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace RothschildStein.H3

/-- The fixed weight-one family consists precisely of horizontal singletons. -/
theorem sum_driftFirstWordFamily {q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : List (Fin (q + 1)) → M) :
    (∑ I ∈ (wordFamily driftWeight 2).filter (fun I => wordWeight driftWeight I = 1), f I) =
      ∑ i : Fin q, f [i.succ] := by
  classical
  let letter : Fin q → List (Fin (q + 1)) := fun i => [i.succ]
  have hinj : Function.Injective letter := by
    intro i j h
    simpa [letter] using h
  have he : (wordFamily driftWeight 2).filter (fun I => wordWeight driftWeight I = 1) =
      (Finset.univ : Finset (Fin q)).image letter := by
    ext I
    simp only [Finset.mem_filter, S.mem_wordFamily_iff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := drift_word_weight_one I h.2
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      simp [letter, wordWeight, driftWeight, Fin.succ_ne_zero]
  rw [he, Finset.sum_image (fun i _ j _ h => hinj h)]

end RothschildStein.H3
