-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BasisExponentialEvaluation
public import RothschildStein.G3.ModelProduct
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

theorem basisWordSubstitution_BCH_input {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f g : formalSpan a s p) :
    basisWordSubstitution D (finiteBCH (basisCoefficientInput D f) (basisCoefficientInput D g)) =
      (modelProduct f g).val := by
  have he := weightedFiniteSubstitutionHom_bch (basisAlphabetWeight D)
    (fun j => finiteBracketWord (modelBasisWord D j))
    (fun j => by
      change FiniteOrderAtLeast (D.weight j) (finiteBracketWord (modelBasisWord D j))
      rw [← modelBasisWord_weight D j]
      exact finiteBracketWord_weight_order p (modelBasisWord D j))
    (basisCoefficientInput_order D f) (basisCoefficientInput_order D g)
  change basisWordSubstitution D _ = finiteBCH (basisWordSubstitution D _)
    (basisWordSubstitution D _) at he
  rw [basisWordSubstitution_input,basisWordSubstitution_input] at he
  exact he

theorem basisWordSubstitution_BCH_exp {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f g : formalSpan a s p) :
    basisWordSubstitution D (finiteExp
      (finiteBCH (basisCoefficientInput D f) (basisCoefficientInput D g))) =
      finiteExp (modelProduct f g).val := by
  have hp := finiteBCH_order (basisCoefficientInput_order D f) (basisCoefficientInput_order D g)
  have hm := map_finiteExp (basisWordSubstitution D) hp (by
    rw [basisWordSubstitution_BCH_input]
    exact formalSpan_positive_order _ (modelProduct f g).property)
  rw [basisWordSubstitution_BCH_input] at hm
  exact hm

theorem differentialWordEvaluation_basis_BCH_exp {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f g : formalSpan a s p) :
    differentialWordEvaluation Ω X hX (finitePolynomial (finiteExp (modelProduct f g).val)) =
      differentialWordEvaluation Ω (fun j => wordBracket X (modelBasisWord D j))
        (fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j))
        (finitePolynomial (finiteExp
          (finiteBCH (basisCoefficientInput D f) (basisCoefficientInput D g)))) := by
  have he := differentialWordEvaluation_finiteBracketAlphabet (basisAlphabetWeight D) Ω X hX
    (modelBasisWord D) (fun j => (modelBasisWord_spec D j).1)
    (modelBasisWord_weight D)
    (finiteExp (finiteBCH (basisCoefficientInput D f) (basisCoefficientInput D g)))
  change differentialWordEvaluation Ω X hX
    (finitePolynomial (basisWordSubstitution D _)) = _ at he
  rw [basisWordSubstitution_BCH_exp] at he
  exact he
end RothschildStein.G3
