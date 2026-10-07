-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BasisBCHExponentialEvaluation
public import RothschildStein.G3.DilatedExponentialEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

theorem differentialWordEvaluation_dilated_basis_BCH_exp {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f g : formalSpan a s p) (δ : ℝ) (q : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX
      (finitePolynomial (finiteExp (coefficientDilationHom δ (modelProduct f g).val))) q).val x =
      (differentialWordEvaluation Ω
        (fun j => δ^D.weight j • wordBracket X (modelBasisWord D j))
        (fun j => ((G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)).const_smul
          (δ^D.weight j)).congr (fun y _ => by ext k; rfl))
        (finitePolynomial (finiteExp
          (finiteBCH (basisCoefficientInput D f) (basisCoefficientInput D g)))) q).val x := by
  let Y := fun i => δ^(p i : ℕ) • X i
  have hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω :=
    fun i => ((hX i).const_smul (δ^(p i : ℕ))).congr (fun y _ => by ext j; rfl)
  let A : WordCoefficients a s p := finiteExp (modelProduct f g).val
  have hd := differentialWordEvaluation_dilatedPolynomial Ω X hX δ A q hx
  change (differentialWordEvaluation Ω X hX
    (finitePolynomial (coefficientDilationHom δ (finiteExp (modelProduct f g).val))) q).val x =
    (differentialWordEvaluation Ω Y hY (finitePolynomial (finiteExp (modelProduct f g).val)) q).val x at hd
  rw [coefficientDilationHom_finiteExp δ (formalSpan_positive_order _ (modelProduct f g).property)] at hd
  rw [differentialWordEvaluation_basis_BCH_exp D Ω Y hY f g] at hd
  have he := differentialWordEvaluation_eqOn Ω
    (fun j => wordBracket Y (modelBasisWord D j))
    (fun j => δ^D.weight j • wordBracket X (modelBasisWord D j))
    (fun j => G1.wordBracket_contDiffOn Ω.isOpen Y hY (modelBasisWord D j))
    (fun j => ((G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)).const_smul
      (δ^D.weight j)).congr (fun y _ => by ext k; rfl))
    (fun j y hy => by
      rw [wordBracket_weighted_scale Ω X hX p δ (modelBasisWord D j) hy,modelBasisWord_weight D j]
      rfl)
  rw [he] at hd
  exact hd
end RothschildStein.G3
