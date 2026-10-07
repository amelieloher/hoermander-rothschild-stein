-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EnumeratedQuasiFactorization
public import RothschildStein.G3.SignedCorrectionSchedules
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Exact total of primitive commutator lengths, one per retained word. -/
def enumeratedPrimitiveArcCount (a s : ℕ) (p : Fin a → ℕ+) : ℕ :=
  ((correctionWordEnumeration a s p s).map (fun I => (G1.commutatorSchedule I).length)).sum

/-- The signs and real coefficients do not change the primitive factor count. -/
theorem signedCorrectionArcSchedule_length_eq_word_sum {a : ℕ}
    (AS : List (ℝ × List (Fin a))) :
    (signedCorrectionArcSchedule AS).length =
      ((AS.map Prod.snd).map (fun I => (G1.commutatorSchedule I).length)).sum := by
  induction AS with
  | nil => rfl
  | cons A AS ih =>
    simp only [signedCorrectionArcSchedule,List.flatMap_cons,List.length_append,
      List.map_cons,List.sum_cons,signedCorrectionSchedule_length] at *
    exact congrArg (fun n => (G1.commutatorSchedule A.2).length+n) ih

/-- Enumerated correction slots have the exact source sum of word lengths. -/
theorem signedCorrectionArcSchedule_length_of_enumeration {a s : ℕ} {p : Fin a → ℕ+}
    (AS : List (ℝ × List (Fin a)))
    (hwords : AS.map Prod.snd = correctionWordEnumeration a s p s) :
    (signedCorrectionArcSchedule AS).length = enumeratedPrimitiveArcCount a s p := by
  rw [signedCorrectionArcSchedule_length_eq_word_sum,hwords]
  rfl
end RothschildStein.G3
