-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedSubstitutionCalculus
public import RothschildStein.G3.ModelBasisWords
public import RothschildStein.G3.QuasiExponentialLeadingWord
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Alphabet weight assigned to each retained homogeneous basis word. -/
def basisAlphabetWeight {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p) :
    Fin (freeDimension a s p) → ℕ+ := fun j => ⟨D.weight j, D.weight_pos j⟩

/-- Weight-preserving substitution of basis letters by their primitive
nested words (BB Lemma 9.22, pp. 413–414). -/
def basisWordSubstitution {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p) :
    FiniteWordAlgebra (freeDimension a s p) s (basisAlphabetWeight D) →ₐ[ℝ]
      FiniteWordAlgebra a s p :=
  weightedFiniteSubstitutionHom (basisAlphabetWeight D)
    (fun j => finiteBracketWord (modelBasisWord D j)) (fun j => by
      change FiniteOrderAtLeast (D.weight j) (finiteBracketWord (modelBasisWord D j))
      rw [← modelBasisWord_weight D j]
      exact finiteBracketWord_weight_order p (modelBasisWord D j))

/-- A finite Lie field is a linear input in the bracket-field alphabet. -/
def basisCoefficientInput {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (f : formalSpan a s p) :
    FiniteWordAlgebra (freeDimension a s p) s (basisAlphabetWeight D) :=
  ∑ j, D.basis.equivFun f j • finiteLetter j

/-- Substitution of the linear bracket-alphabet input gives exactly
the original finite free Lie coefficient. -/
theorem basisWordSubstitution_input {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    basisWordSubstitution D (basisCoefficientInput D f) =
      (f.val : FiniteWordAlgebra a s p) := by
  unfold basisWordSubstitution basisCoefficientInput
  rw [map_sum]
  simp only [map_smul, weightedFiniteSubstitutionHom_letter]
  have he := congrArg (fun h : formalSpan a s p => h.val) (D.basis.sum_equivFun f)
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at he
  change (∑ j, D.basis.equivFun f j •
    (truncatedBracket (modelBasisWord D j) : WordCoefficients a s p)) = f.val
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  rw [(modelBasisWord_spec D j).2.2]
end RothschildStein.G3
