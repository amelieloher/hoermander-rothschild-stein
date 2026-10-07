-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelBasisWords
public import RothschildStein.G3.BracketPolynomialCoefficients
public import RothschildStein.G3.FinitePolynomialLinear
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Actual vector field attached to a finite free Lie coefficient,
using a fixed homogeneous commutator basis (BB Lemma 9.22, pp. 413–414). -/
def finiteLieField {a s N : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) (f : formalSpan a s p) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  fun x => ∑ j, D.basis.equivFun f j • wordBracket X (modelBasisWord D j) x

/-- The chosen finite Lie field is smooth on the primitive coefficient
domain; no independence of the actual primitive fields is assumed. -/
theorem finiteLieField_contDiffOn {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (finiteLieField D X f) Ω := by
  apply ContDiffOn.sum
  intro j _
  exact (G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)).const_smul _

/-- Finite Lie polynomials evaluated as actual differential operators
are precisely directional differentiation along their associated fields.
This identity includes derivatives of every variable primitive coefficient. -/
theorem differentialWordEvaluation_finiteLieField {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p)
    (g : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX (finitePolynomial f.val) g).val x =
      fderiv ℝ g.val x (finiteLieField D X f x) := by
  have he := congrArg (fun h : formalSpan a s p => h.val) (D.basis.sum_equivFun f)
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at he
  have hp := congrArg (finitePolynomialLinear (a := a) (s := s) (p := p)) he
  rw [map_sum] at hp
  simp only [map_smul] at hp
  change (∑ j, D.basis.equivFun f j • finitePolynomial (D.basis j).val) =
    finitePolynomial f.val at hp
  rw [← hp, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply]
  unfold finiteLieField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(modelBasisWord_spec D j).2.2,
    differentialWordEvaluation_truncatedBracket Ω X hX (modelBasisWord D j)
      (modelBasisWord_spec D j).1 (modelBasisWord_spec D j).2.1,
    smoothFieldOperator_apply Ω _ _ g hx, map_smul]
  rfl
end RothschildStein.G3
