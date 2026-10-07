-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedPrimitiveSchedules
public import RothschildStein.G3.ActualQuasiExponentialPoints
@[expose] public section
noncomputable section
namespace RothschildStein.G3

def rootTimedPrimitiveSchedule {a : ℕ} (p : Fin a → ℕ+)
    (A : ℝ × List (Fin a)) : List (Fin a × ℝ) :=
  let t := |A.1| ^ ((wordWeight p A.2 : ℝ)⁻¹)
  (signedCorrectionSchedule A).map
    (fun b => (b.1,if b.2 then t^(p b.1 : ℕ) else -(t^(p b.1 : ℕ))))

def rootTimedFactorSchedule {a : ℕ} (p : Fin a → ℕ+)
    (AS : List (ℝ × List (Fin a))) : List (Fin a × ℝ) :=
  AS.flatMap (rootTimedPrimitiveSchedule p)

theorem rootTimedPrimitiveSchedule_length {a : ℕ} (p : Fin a → ℕ+)
    (A : ℝ × List (Fin a)) :
    (rootTimedPrimitiveSchedule p A).length = (signedCorrectionSchedule A).length := by
  simp only [rootTimedPrimitiveSchedule,List.length_map]

theorem rootTimedFactorSchedule_length {a : ℕ} (p : Fin a → ℕ+)
    (AS : List (ℝ × List (Fin a))) :
    (rootTimedFactorSchedule p AS).length = (signedCorrectionArcSchedule AS).length := by
  induction AS with
  | nil => rfl
  | cons A AS ih =>
    simp only [rootTimedFactorSchedule,signedCorrectionArcSchedule,List.flatMap_cons,
      List.length_append,rootTimedPrimitiveSchedule_length] at *
    rw [ih]

end RothschildStein.G3
