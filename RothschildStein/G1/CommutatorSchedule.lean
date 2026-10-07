-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.IntegralCurveCosts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Inverse generator-arc schedule: reverse the list and flip signs
(BB Def 1.46, p. 26, eq. (1.23)). -/
def inverseSchedule {ι : Type*} (S : List (ι × Bool)) : List (ι × Bool) :=
  S.reverse.map (fun a => (a.1, !a.2))

/-- The independent-parameter commutator schedule in application order:
outer positive arc, tail, outer negative arc, inverse tail. The labels include
both a generator and its independent parameter index
(BB pp. 26, 29–30, eqs. (1.23), (1.32)). -/
def commutatorSchedule {ι : Type*} : List ι → List (ι × Bool)
  | [] => []
  | [i] => [(i, true)]
  | i :: j :: I => [(i, true)] ++ commutatorSchedule (j :: I) ++
      [(i, false)] ++ inverseSchedule (commutatorSchedule (j :: I))

/-- Inverting a schedule twice recovers the schedule (BB p. 26). -/
theorem inverseSchedule_inverse {ι : Type*} (S : List (ι × Bool)) :
    inverseSchedule (inverseSchedule S) = S := by
  simp [inverseSchedule, List.map_reverse, List.map_map, Function.comp_def]

/-- Schedule inversion preserves the generator arc count (BB p. 26). -/
theorem inverseSchedule_length {ι : Type*} (S : List (ι × Bool)) :
    (inverseSchedule S).length = S.length := by simp only [inverseSchedule, List.length_map, List.length_reverse]

/-- A nonempty commutator of length l uses exactly 3*2^(l-1)-2
arcs, expressed without truncated subtraction (BB Rem 1.47, p. 26). -/
theorem commutatorSchedule_length {ι : Type*} (I : List ι) (hI : I ≠ []) :
    (commutatorSchedule I).length + 2 = 3 * 2 ^ (I.length - 1) := by
  induction I with
  | nil => exact (hI rfl).elim
  | cons i I ih =>
    cases I with
    | nil => norm_num [commutatorSchedule]
    | cons j I =>
      have hh := ih (by simp)
      simp only [commutatorSchedule, List.length_append, List.length_cons,
        List.length_nil, inverseSchedule_length] at *
      simp only [Nat.add_sub_cancel, pow_succ] at *
      omega

/-- Evaluate an arc schedule in the order in which its arcs are
traversed (BB Def 1.46, p. 26). -/
def runSchedule {ι E : Type*} (A : ι × Bool → E → E) : List (ι × Bool) → E → E
  | [], x => x
  | a :: S, x => runSchedule A S (A a x)

/-- Appending schedules composes their actual maps (BB p. 26). -/
theorem runSchedule_append {ι E : Type*} (A : ι × Bool → E → E)
    (S T : List (ι × Bool)) (x : E) :
    runSchedule A (S ++ T) x = runSchedule A T (runSchedule A S x) := by
  induction S generalizing x with
  | nil => rfl
  | cons a S ih => exact ih (A a x)

/-- Reversibility is required only along the actual finite trajectory,
not as a global inverse assertion (BB Lemma 1.52, pp. 30–31). -/
def ScheduleReversible {ι E : Type*} (A : ι × Bool → E → E) : List (ι × Bool) → E → Prop
  | [], _ => True
  | a :: S, x => A (a.1, !a.2) (A a x) = x ∧ ScheduleReversible A S (A a x)

/-- Reversing actual locally reversible arcs gives an inverse at the
starting point (BB pp. 26, 30–31). -/
theorem runSchedule_inverse_of_reversible {ι E : Type*} (A : ι × Bool → E → E)
    (S : List (ι × Bool)) (x : E) (h : ScheduleReversible A S x) :
    runSchedule A (inverseSchedule S) (runSchedule A S x) = x := by
  induction S generalizing x with
  | nil => rfl
  | cons a S ih =>
    have he : inverseSchedule (a :: S) = inverseSchedule S ++ [(a.1, !a.2)] := by
      simp only [inverseSchedule, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    rw [he, runSchedule_append, runSchedule]
    change A (a.1, !a.2) (runSchedule A (inverseSchedule S) (runSchedule A S (A a x))) = x
    rw [ih (A a x) h.2]
    exact h.1

end RothschildStein.G1
