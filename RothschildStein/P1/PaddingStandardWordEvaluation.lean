-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingLieWordEvaluation
public import RothschildStein.Definitions.wordBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

private def standardLieWord {q : ℕ} : List (Fin (q + 1)) → Hormander.Interface.LieWord q
  | [] => .generator 0
  | [i] => .generator i
  | i :: j :: I => .bracket (.generator i) (standardLieWord (j :: I))

private theorem standardLieWord_eval_cons {q n : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) :
    ∀ I : List (Fin (q + 1)), ∀ i,
      Hormander.Interface.LieWord.eval X (standardLieWord (i :: I)) = wordBracket X (i :: I) := by
  intro I
  induction I with
  | nil => intro i; rfl
  | cons j I ih =>
      intro i
      simp only [standardLieWord, Hormander.Interface.LieWord.eval, wordBracket, ih]

private theorem standardLieWord_padding_cons {q d : ℕ} :
    ∀ I : List (Fin (q + 1)), ∀ i,
      standardLieWord ((i :: I).map (paddingGeneratorIndex (d := d))) =
        paddingLieWord (standardLieWord (i :: I)) := by
  intro I
  induction I with
  | nil => intro i; rfl
  | cons j I ih =>
      intro i
      change (Hormander.Interface.LieWord.generator (paddingGeneratorIndex i)).bracket
        (standardLieWord ((j :: I).map paddingGeneratorIndex)) =
        (Hormander.Interface.LieWord.generator (paddingGeneratorIndex i)).bracket
          (paddingLieWord (standardLieWord (j :: I)))
      rw [ih j]

/-- Every standard word in the original generators
extends with zero added components. This reuses the proved Lie-word
transport and applies to the exact word carrier in StepSpansAt. -/
theorem wordBracket_padding_map {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : List (Fin (q + 1))) :
    EqOn (wordBracket (paddingVectorFields (d := d) X)
      (I.map (paddingGeneratorIndex (d := d))))
      (paddingBaseField (d := d) (wordBracket X I)) ((paddingBaseCLM n d) ⁻¹' Ω) := by
  cases I with
  | nil =>
      intro ξ _
      change (0 : Fin (n + d) → ℝ) = joinPoint (0 : Fin n → ℝ) (0 : Fin d → ℝ)
      rw [← paddingJoinCLM_apply n d 0 0]
      exact (paddingJoinCLM n d).map_zero.symm
  | cons i I =>
      intro ξ hξ
      have h := lieWordEval_paddingLieWord Ω hΩ X hX (standardLieWord (i :: I)) hξ
      rw [← standardLieWord_padding_cons I i] at h
      rw [show ((i :: I).map (paddingGeneratorIndex (d := d))) =
        paddingGeneratorIndex i :: I.map (paddingGeneratorIndex (d := d)) from rfl] at h
      rw [standardLieWord_eval_cons, standardLieWord_eval_cons] at h
      exact h

end RothschildStein.P1
