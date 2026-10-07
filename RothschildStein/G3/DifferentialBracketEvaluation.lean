-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialWordEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Finite associative polynomial for a nested commutator, before
truncation (BB Lemma 9.22, pp. 413–414). -/
def bracketWordPolynomial {a : ℕ} :
    List (Fin a) → MonoidAlgebra ℝ (FreeMonoid (Fin a))
  | [] => 0
  | [i] => MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ)
  | i :: j :: I =>
      ⁅MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ), bracketWordPolynomial (j :: I)⁆

/-- Formal commutator polynomials evaluate to the actual nested field
brackets, including all derivatives of variable field coefficients
(BB Lemma 9.22, pp. 413–414). -/
theorem differentialWordEvaluation_bracketWord {a N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (hne : I ≠ []) :
    differentialWordEvaluation Ω X hX (bracketWordPolynomial I) =
      smoothFieldOperator Ω (wordBracket X I)
        (G1.wordBracket_contDiffOn Ω.isOpen X hX I) := by
  induction I with
  | nil => exact False.elim (hne rfl)
  | cons i I ih =>
    cases I with
    | nil =>
      change differentialWordEvaluation Ω X hX
        (MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ)) = _
      rw [differentialWordEvaluation, MonoidAlgebra.lift_single,
        FreeMonoid.lift_eval_of, one_smul]
      rfl
    | cons j I =>
      have ht := ih (List.cons_ne_nil j I)
      change differentialWordEvaluation Ω X hX
        ⁅MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ), bracketWordPolynomial (j :: I)⁆ = _
      simp only [Ring.lie_def, map_sub, map_mul]
      rw [ht]
      have hi : differentialWordEvaluation Ω X hX
          (MonoidAlgebra.single (FreeMonoid.of i) (1 : ℝ)) = smoothFieldOperator Ω (X i) (hX i) := by
        rw [differentialWordEvaluation, MonoidAlgebra.lift_single,
          FreeMonoid.lift_eval_of, one_smul]
      rw [hi]
      exact (smoothFieldOperator_lieBracket Ω (X i) (wordBracket X (j :: I))
        (hX i) (G1.wordBracket_contDiffOn Ω.isOpen X hX (j :: I))).symm
end RothschildStein.G3
