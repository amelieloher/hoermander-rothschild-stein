-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DilatedPolynomialEvaluation
public import RothschildStein.G3.BasisExponentialEvaluation
public import RothschildStein.G3.DifferentialEvaluationLocality
public import RothschildStein.G3.QuasiDilationOrder
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Weighted coefficient dilation commutes with finite exponentiation. -/
theorem coefficientDilationHom_finiteExp {a s : ℕ} {p : Fin a → ℕ+}
    (δ : ℝ) {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) :
    coefficientDilationHom δ (finiteExp f) = finiteExp (coefficientDilationHom δ f) :=
  map_finiteExp _ hf (finiteDilate_weight_order δ hf)

/-- The finite exponential of a dilated free Lie coefficient is
exactly the low-weight exponential evaluated in weighted bracket fields.
This identifies the actual comparison operator without expanding long
products of brackets into primitive words (BB Lemma 9.22). -/
theorem differentialWordEvaluation_dilated_basis_exp {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f : formalSpan a s p) (δ : ℝ) (g : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX
      (finitePolynomial (finiteExp (coefficientDilationHom δ f.val))) g).val x =
      (differentialWordEvaluation Ω
        (fun j => δ ^ D.weight j • wordBracket X (modelBasisWord D j))
        (fun j => ((G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)).const_smul (δ ^ D.weight j)).congr (fun y _ => by ext k; rfl))
        (finitePolynomial (finiteExp (basisCoefficientInput D f))) g).val x := by
  let Y := fun i => δ ^ (p i : ℕ) • X i
  have hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω :=
    fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl)
  let A : WordCoefficients a s p := finiteExp f.val
  have hd := differentialWordEvaluation_dilatedPolynomial Ω X hX δ A g hx
  change (differentialWordEvaluation Ω X hX
    (finitePolynomial (coefficientDilationHom δ (finiteExp f.val))) g).val x =
    (differentialWordEvaluation Ω Y hY (finitePolynomial (finiteExp f.val)) g).val x at hd
  rw [coefficientDilationHom_finiteExp δ (formalSpan_positive_order f.val f.property)] at hd
  rw [differentialWordEvaluation_basis_exp D Ω Y hY f] at hd
  have he := differentialWordEvaluation_eqOn Ω
    (fun j => wordBracket Y (modelBasisWord D j))
    (fun j => δ ^ D.weight j • wordBracket X (modelBasisWord D j))
    (fun j => G1.wordBracket_contDiffOn Ω.isOpen Y hY (modelBasisWord D j))
    (fun j => ((G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)).const_smul (δ ^ D.weight j)).congr (fun y _ => by ext k; rfl))
    (fun j y hy => by
      rw [wordBracket_weighted_scale Ω X hX p δ (modelBasisWord D j) hy,
        modelBasisWord_weight D j]
      rfl)
  rw [he] at hd
  exact hd
end RothschildStein.G3
