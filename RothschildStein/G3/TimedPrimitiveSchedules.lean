-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SignedCorrectionSchedules
@[expose] public section
noncomputable section
namespace RothschildStein.G3

def runTimedPrimitiveSchedule {a : ℕ} {E : Type*} (Φ : Fin a → E × ℝ → E) :
    List (Fin a × ℝ) → E → E
  | [], x => x
  | b :: S, x => runTimedPrimitiveSchedule Φ S (Φ b.1 (x,b.2))

def padTimedPrimitiveSchedule {a : ℕ} (i : Fin a) (L : ℕ)
    (S : List (Fin a × ℝ)) : List (Fin a × ℝ) :=
  S++List.replicate (L-S.length) (i,0)

theorem padTimedPrimitiveSchedule_length {a : ℕ} (i : Fin a) {L : ℕ}
    (S : List (Fin a × ℝ)) (hS : S.length ≤ L) :
    (padTimedPrimitiveSchedule i L S).length = L := by
  simp only [padTimedPrimitiveSchedule,List.length_append,List.length_replicate]
  omega

end RothschildStein.G3
