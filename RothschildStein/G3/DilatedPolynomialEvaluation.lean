-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialPolynomialBounds
public import RothschildStein.G3.FiniteLieFieldDilation
public import RothschildStein.G3.WeightedBracketScaling
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Dilating finite coefficients is exactly weighted scaling of
primitive fields in actual differential evaluation (BB Lemma 9.22). -/
theorem differentialWordEvaluation_dilatedPolynomial {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (δ : ℝ) (A : WordCoefficients a s p) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX (finitePolynomial (finiteDilate δ A)) f).val x =
      (differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        (finitePolynomial A) f).val x := by
  rw [differentialWordEvaluation_finitePolynomial_apply Ω X hX _ f hx,
    differentialWordEvaluation_finitePolynomial_apply Ω _ _ A f hx]
  apply Finset.sum_congr rfl
  intro J _
  rw [wordDerivative_weighted_scale Ω X hX p δ J.val f.val f.property hx]
  change (δ ^ wordWeight p J.val * A J) * _ = A J * (δ ^ wordWeight p J.val * _)
  ring

/-- A dilated finite Lie coefficient is the corresponding weighted
constant combination of its retained bracket fields. -/
theorem dilatedLieField_eq_weighted_combination {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (f : formalSpan a s p) (δ : ℝ) :
    finiteLieField D X ⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩ =
      fun x => ∑ j, D.basis.equivFun f j •
        (δ ^ D.weight j • wordBracket X (modelBasisWord D j) x) := by
  funext x
  simp only [finiteLieField, basis_equivFun_dilated, coordinateDilation]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_smul]
  congr 1
  ring
end RothschildStein.G3
