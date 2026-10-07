-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakWordWeightCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3

/-- The complete weight-two family consists of the drift singleton
and every ordered pair of horizontal letters. -/
theorem drift_word_weight_two {q : ℕ} (I : List (Fin (q+1)))
    (hI : wordWeight driftWeight I = 2) :
    I = [0] ∨ ∃ i j : Fin q, I = [i.succ,j.succ] := by
  have hl := S.length_le_wordWeight driftWeight I
  cases I with
  | nil => simp [wordWeight] at hI
  | cons i J =>
    cases J with
    | nil =>
      left
      have hi : i = 0 := by
        by_contra hn
        obtain ⟨j,hj⟩ := Fin.exists_succ_eq_of_ne_zero hn
        subst i
        simp [wordWeight,driftWeight,Fin.succ_ne_zero] at hI
      rw [hi]
    | cons j K =>
      have hK : K = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hl
        omega)
      subst K
      have hi : i ≠ 0 := by
        intro hz
        subst i
        simp [wordWeight,driftWeight] at hI
      have hj : j ≠ 0 := by
        intro hz
        subst j
        simp [wordWeight,driftWeight] at hI
      obtain ⟨a,ha⟩ := Fin.exists_succ_eq_of_ne_zero hi
      obtain ⟨b,hb⟩ := Fin.exists_succ_eq_of_ne_zero hj
      exact Or.inr ⟨a,b,by rw [ha,hb]⟩

end RothschildStein.H3
