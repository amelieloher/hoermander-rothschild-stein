-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteBracketAlphabetEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- The bracket-alphabet coefficient input has positive order. -/
theorem basisCoefficientInput_order {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    FiniteOrderAtLeast 1 (basisCoefficientInput D f) := by
  unfold basisCoefficientInput
  apply finiteOrderAtLeast_sum
  intro j _
  exact finiteOrderAtLeast_smul (finiteLetter_order j) _

/-- The finite exponential of a bracket-basis input maps to the
finite exponential of the original Lie coefficient (BB Lemma 9.22). -/
theorem basisWordSubstitution_exp_input {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    basisWordSubstitution D (finiteExp (basisCoefficientInput D f)) =
      finiteExp (f.val : FiniteWordAlgebra a s p) := by
  have h := map_finiteExp (basisWordSubstitution D) (basisCoefficientInput_order D f)
    (by rw [basisWordSubstitution_input]; exact formalSpan_positive_order f.val f.property)
  rw [basisWordSubstitution_input] at h
  exact h

/-- Actual differential evaluation of the finite Lie exponential
agrees with the low-weight exponential in the bracket-field alphabet,
whose ordinary factor count preserves the finite jet budget. -/
theorem differentialWordEvaluation_basis_exp {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p) :
    differentialWordEvaluation Ω X hX (finitePolynomial (finiteExp f.val)) =
      differentialWordEvaluation Ω (fun j => wordBracket X (modelBasisWord D j))
        (fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j))
        (finitePolynomial (finiteExp (basisCoefficientInput D f))) := by
  have h := differentialWordEvaluation_finiteBracketAlphabet (basisAlphabetWeight D) Ω X hX
    (modelBasisWord D) (fun j => (modelBasisWord_spec D j).1)
    (modelBasisWord_weight D) (finiteExp (basisCoefficientInput D f))
  change differentialWordEvaluation Ω X hX
    (finitePolynomial (basisWordSubstitution D (finiteExp (basisCoefficientInput D f)))) = _ at h
  rw [basisWordSubstitution_exp_input] at h
  exact h
end RothschildStein.G3
