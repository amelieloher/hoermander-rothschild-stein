-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FixedQuasiFactorization
public import RothschildStein.G1.CommutatorSchedule
@[expose] public section
noncomputable section
namespace RothschildStein.G3

def signedCorrectionSchedule {a : ℕ} (A : ℝ × List (Fin a)) : List (Fin a × Bool) :=
  if 0 ≤ A.1 then G1.commutatorSchedule A.2
  else G1.inverseSchedule (G1.commutatorSchedule A.2)

theorem signedCorrectionSchedule_length {a : ℕ} (A : ℝ × List (Fin a)) :
    (signedCorrectionSchedule A).length = (G1.commutatorSchedule A.2).length := by
  unfold signedCorrectionSchedule
  split
  · rfl
  · exact G1.inverseSchedule_length _

def signedCorrectionArcSchedule {a : ℕ} (AS : List (ℝ × List (Fin a))) :
    List (Fin a × Bool) := AS.flatMap signedCorrectionSchedule

end RothschildStein.G3
