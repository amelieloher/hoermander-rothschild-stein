-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.bracketSpansOn

/-! # Embedding right-nested words in binary Lie words

The empty word is represented by a self-bracket, whose evaluation is zero.
Every nonempty right-nested word retains its value under the embedding.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein Hormander.Interface

/-- Embed a list of generators as a right-nested binary Lie word. -/
def listLieWord {q k : ℕ} (σ : Fin q → Fin (k + 1)) : List (Fin q) → LieWord k
  | [] => .bracket (.generator 0) (.generator 0)
  | [i] => .generator (σ i)
  | i :: j :: w => .bracket (.generator (σ i)) (listLieWord σ (j :: w))

/-- Evaluation of the embedded binary word is the original right-nested bracket. -/
theorem eval_listLieWord {q k n : ℕ} (σ : Fin q → Fin (k + 1))
    (X : Fin (k + 1) → (Fin n → ℝ) → Fin n → ℝ) (w : List (Fin q)) :
    LieWord.eval X (listLieWord σ w) = wordBracket (fun i => X (σ i)) w := by
  induction w with
  | nil => simp [listLieWord, LieWord.eval, wordBracket]
  | cons i w ih =>
      cases w with
      | nil => rfl
      | cons j w =>
          change VectorField.lieBracket ℝ (X (σ i)) (LieWord.eval X (listLieWord σ (j :: w))) = _
          rw [ih]
          rfl

/-- Reindexing generators reindexes every right-nested word. -/
theorem wordBracket_map {p q n : ℕ} (σ : Fin p → Fin q)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ) (w : List (Fin p)) :
    wordBracket X (w.map σ) = wordBracket (fun i => X (σ i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      cases w with
      | nil => rfl
      | cons j w =>
          change VectorField.lieBracket ℝ (X (σ i)) (wordBracket X ((j :: w).map σ)) = _
          rw [ih]
          rfl

/-- Spanning by right-nested brackets implies the binary Lie-word spanning condition. -/
theorem lieAlgebraSpansOn_of_bracketSpansOn {k n : ℕ} {Ω : Set (Fin n → ℝ)}
    (X : Fin (k + 1) → (Fin n → ℝ) → Fin n → ℝ) (hX : bracketSpansOn Ω X) :
    LieAlgebraSpansOn Ω X := by
  intro x hx
  apply top_unique
  rw [← hX x hx]
  apply Submodule.span_le.mpr
  rintro v ⟨w, _, rfl⟩
  have heq := congrFun (eval_listLieWord id X w) x
  simp only [id_eq] at heq
  rw [← heq]
  exact Submodule.subset_span ⟨listLieWord id w, rfl⟩

end HeatKernel
