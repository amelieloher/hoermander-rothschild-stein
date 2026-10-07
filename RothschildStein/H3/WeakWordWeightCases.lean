-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.driftWeight
public import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- A word in positive weights has weight zero only when it is empty. -/
theorem word_eq_nil_of_weight_zero {m : ℕ} (w : Fin m → ℕ+)
    (I : List (Fin m)) (hI : wordWeight w I = 0) : I = [] := by
  apply List.eq_nil_of_length_eq_zero
  have hl := S.length_le_wordWeight w I
  omega

/-- A drift-weight word of weight one is exactly one horizontal letter. -/
theorem drift_word_weight_one {q : ℕ} (I : List (Fin (q+1)))
    (hI : wordWeight driftWeight I = 1) : ∃ i : Fin q, I = [i.succ] := by
  have hl := S.length_le_wordWeight driftWeight I
  cases I with
  | nil => simp [wordWeight] at hI
  | cons j J =>
    have hJ : J = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_cons] at hl
      omega)
    subst J
    have hj : j ≠ 0 := by
      intro he
      subst j
      simp [wordWeight,driftWeight] at hI
    obtain ⟨i,hi⟩ := Fin.exists_succ_eq_of_ne_zero hj
    exact ⟨i,by rw [hi]⟩

end RothschildStein.H3
