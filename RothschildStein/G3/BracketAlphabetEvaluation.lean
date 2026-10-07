-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.AssociativeWordSubstitution
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Substituting nested bracket polynomials and then evaluating in
primitive fields agrees exactly with evaluation in the bracket-field
alphabet, including derivatives of variable coefficients (BB Lemma 9.22). -/
theorem differentialWordEvaluation_bracketAlphabet {a b N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin b → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : Fin a → List (Fin b)) (hne : ∀ i, I i ≠ []) :
    (differentialWordEvaluation Ω X hX).comp
      (associativeWordSubstitution (fun i => bracketWordPolynomial (I i))) =
      differentialWordEvaluation Ω (fun i => wordBracket X (I i))
        (fun i => G1.wordBracket_contDiffOn Ω.isOpen X hX (I i)) := by
  rw [associativeWordSubstitution_evaluation (fun i => bracketWordPolynomial (I i))
    (differentialWordEvaluation Ω X hX)]
  have he : (fun i => differentialWordEvaluation Ω X hX (bracketWordPolynomial (I i))) =
      (fun i => smoothFieldOperator Ω (wordBracket X (I i))
        (G1.wordBracket_contDiffOn Ω.isOpen X hX (I i))) := by
    funext i
    exact differentialWordEvaluation_bracketWord Ω X hX (I i) (hne i)
  rw [he]
  rfl
end RothschildStein.G3
