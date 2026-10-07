-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftSecondWeakNorm
public import RothschildStein.H3.DriftWeightTwoCases
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace RothschildStein.H3

/-- Exact sum over the fixed weight-two family: the drift
singleton and each ordered pair of horizontal letters occur once. -/
theorem sum_driftSecondWordFamily {q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : List (Fin (q + 1)) → M) :
    (∑ I ∈ driftSecondWordFamily q, f I) =
      f [0] + ∑ i : Fin q, ∑ j : Fin q, f [i.succ, j.succ] := by
  classical
  let pair : Fin q × Fin q → List (Fin (q + 1)) := fun p => [p.1.succ, p.2.succ]
  have hinj : Function.Injective pair := by
    intro a b h
    cases a
    cases b
    simpa [pair] using h
  have hn : [0] ∉ (Finset.univ : Finset (Fin q × Fin q)).image pair := by
    simp [pair]
  have he : driftSecondWordFamily q =
      insert [0] ((Finset.univ : Finset (Fin q × Fin q)).image pair) := by
    ext I
    rw [mem_driftSecondWordFamily_iff, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hI
      rcases drift_word_weight_two I hI with hz | ⟨i, j, hp⟩
      · exact Or.inl hz
      · exact Or.inr ⟨(i, j), Finset.mem_univ _, hp.symm⟩
    · rintro (rfl | ⟨p, _, hp⟩)
      · simp [wordWeight, driftWeight]
      · rw [← hp]
        simp [pair, wordWeight, driftWeight]
  rw [he, Finset.sum_insert hn, Finset.sum_image (fun a _ b _ h => hinj h)]
  simp only [pair, Fintype.sum_prod_type]

end RothschildStein.H3
