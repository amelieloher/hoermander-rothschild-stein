-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Algebra.Lie.Basic
public import RothschildStein.G3.FiniteWords
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A nonempty right-nested word on an arbitrary alphabet
(BB Lemma 1.21, p. 12). -/
inductive Nested (α : Type*)
  | letter : α → Nested α
  | bracket : α → Nested α → Nested α

/-- The actual letters of a right-nested word (BB p. 12). -/
def Nested.letters {α : Type*} : Nested α → List α
  | .letter i => [i]
  | .bracket i u => i :: u.letters

/-- Evaluation in any Lie ring (BB Lemma 1.21, p. 12). -/
def Nested.eval {α L : Type*} [LieRing L] (X : α → L) : Nested α → L
  | .letter i => X i
  | .bracket i u => ⁅X i, u.eval X⁆

/-- Integer linear combinations of right-nested words (BB p. 12). -/
def evaluateCombination {α L : Type*} [LieRing L] (X : α → L)
    (c : List (ℤ × Nested α)) : L := (c.map fun z => z.1 • z.2.eval X).sum

/-- Jacobi's recursive integer expansion of a bracket (BB (1.13), p. 12). -/
def normalizeBracket {α : Type*} : Nested α → Nested α → List (ℤ × Nested α)
  | .letter i, v => [(1, .bracket i v)]
  | .bracket i u, v =>
      ((normalizeBracket u v).map fun z => (z.1, .bracket i z.2)) ++
      ((normalizeBracket u (.bracket i v)).map fun z => (-z.1, z.2))

/-- Prefixing distributes over integer combinations (BB p. 12). -/
theorem evaluateCombination_prefix {α L : Type*} [LieRing L] (X : α → L)
    (i : α) (c : List (ℤ × Nested α)) :
    evaluateCombination X (c.map fun z => (z.1, Nested.bracket i z.2)) =
      ⁅X i, evaluateCombination X c⁆ := by
  induction c with
  | nil => simp [evaluateCombination]
  | cons z c ih =>
    simp only [evaluateCombination, List.map_cons, List.map_map, List.sum_cons,
      Nested.eval] at *
    rw [ih, lie_add, lie_zsmul]

/-- Negating coefficients negates the represented Lie polynomial (BB p. 12). -/
theorem evaluateCombination_neg {α L : Type*} [LieRing L] (X : α → L)
    (c : List (ℤ × Nested α)) :
    evaluateCombination X (c.map fun z => (-z.1, z.2)) = -evaluateCombination X c := by
  simp [evaluateCombination, List.map_map, Function.comp_def, List.sum_neg]

/-- The recursive integer combination evaluates to the original bracket,
with no analytic or field hypotheses (BB Lemma 1.21 and (1.13), p. 12). -/
theorem normalizeBracket_eval {α L : Type*} [LieRing L] (X : α → L)
    (u v : Nested α) : evaluateCombination X (normalizeBracket u v) = ⁅u.eval X, v.eval X⁆ := by
  induction u generalizing v with
  | letter i => simp [normalizeBracket, evaluateCombination, Nested.eval]
  | bracket i u ih =>
    change evaluateCombination X
      (((normalizeBracket u v).map fun z => (z.1, Nested.bracket i z.2)) ++
        ((normalizeBracket u (.bracket i v)).map fun z => (-z.1, z.2))) = _
    rw [show ∀ c d, evaluateCombination X (c ++ d) =
      evaluateCombination X c + evaluateCombination X d from
        fun c d => by simp [evaluateCombination],
      evaluateCombination_prefix, evaluateCombination_neg, ih, ih]
    simp only [Nested.eval, ← sub_eq_add_neg, lie_lie]

/-- Every summand retains the same multiset of leaves
(BB Lemma 1.21, p. 12). -/
theorem normalizeBracket_letters {α : Type*} (u v : Nested α) :
    ∀ z ∈ normalizeBracket u v, z.2.letters.Perm (u.letters ++ v.letters) := by
  induction u generalizing v with
  | letter i =>
    intro z hz
    simp only [normalizeBracket, List.mem_singleton] at hz
    subst z
    simp [Nested.letters]
  | bracket i u ih =>
    intro z hz
    simp only [normalizeBracket, List.mem_append] at hz
    rcases hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      exact List.Perm.cons i (ih v w hw)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have h := ih (.bracket i v) w hw
      exact h.trans (by
        simp only [Nested.letters]
        exact List.perm_append_comm.trans (List.Perm.cons i List.perm_append_comm))

end RothschildStein.G3
