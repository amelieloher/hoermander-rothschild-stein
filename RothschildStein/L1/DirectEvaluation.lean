-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.UnrestrictedFormalCoefficients
public import RothschildStein.G3.BracketPolynomialCoefficients
public import RothschildStein.G3.FinitePolynomialLinear
public import Mathlib.Analysis.Calculus.FDeriv.Linear
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Coordinate test functions on the primitive smooth domain. -/
def coordinateTest {N : ℕ} (Ω : Opens (Fin N → ℝ)) (j : Fin N) : smoothOnFunctions Ω :=
  let q : (Fin N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  ⟨q,q.contDiff.contDiffOn⟩

/-- Direct formal tangent evaluation, with no constraint on cutoff versus
individual generator weights (BB Definition 10.10, p. 487). -/
def directPointEvaluation {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (x : Fin N → ℝ) :
    formalSpan a s p →ₗ[ℝ] (Fin N → ℝ) where
  toFun f j := ((differentialWordEvaluation Ω X hX (finitePolynomialLinear f.val))
    (coordinateTest Ω j)).val x
  map_add' f g := by
    ext j
    simp only [Submodule.coe_add,map_add,LinearMap.add_apply,Pi.add_apply]
  map_smul' r f := by
    ext j
    simp only [Submodule.coe_smul,map_smul,LinearMap.smul_apply,Pi.smul_apply,RingHom.id_apply]

/-- Direct evaluation recovers the actual retained nested word. -/
theorem directPointEvaluation_word {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    directPointEvaluation (s := s) (p := p) Ω X hX x (wordLieElement I) = wordBracket X I x := by
  classical
  by_cases he : I = []
  · subst I
    have hz : (wordLieElement [] : formalSpan a s p) = 0 := by apply Subtype.ext; rfl
    rw [hz,map_zero]
    rfl
  · ext j
    change ((differentialWordEvaluation Ω X hX (finitePolynomial (truncatedBracket I)))
      (coordinateTest Ω j)).val x = _
    rw [differentialWordEvaluation_truncatedBracket Ω X hX I he hI]
    change (if x ∈ Ω then fieldDerivative (wordBracket X I) (coordinateTest Ω j).val x else 0) = _
    rw [ite_eq_left hx]
    change fderiv ℝ (ContinuousLinearMap.proj j : (Fin N → ℝ) → ℝ) x (wordBracket X I x) = _
    rw [ContinuousLinearMap.fderiv]
    rfl
end RothschildStein.L1
