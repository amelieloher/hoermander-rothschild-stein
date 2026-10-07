-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluation
public import RothschildStein.G3.FiniteLieFields
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Direct actual evaluation equals the finite Lie field in the chosen basis. -/
theorem directPointEvaluation_eq_finiteLieField {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    directPointEvaluation Ω X hX x f = finiteLieField D X f x := by
  ext j
  change ((differentialWordEvaluation Ω X hX (finitePolynomial f.val)) (coordinateTest Ω j)).val x = _
  rw [differentialWordEvaluation_finiteLieField D Ω X hX f (coordinateTest Ω j) hx]
  change fderiv ℝ ((ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ) : (Fin N → ℝ) → ℝ) x
    (finiteLieField D X f x) = _
  rw [ContinuousLinearMap.fderiv]
  rfl

/-- Every retained word is an actual constant linear combination
of the chosen formal basis words, throughout the entire smooth domain. -/
theorem wordBracket_eq_formal_basis_sum {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    wordBracket X I x = ∑ j, D.basis.equivFun (wordLieElement I) j •
      wordBracket X (modelBasisWord D j) x := by
  rw [← directPointEvaluation_word Ω X hX I hI hx,
    directPointEvaluation_eq_finiteLieField D Ω X hX _ hx]
  rfl
end RothschildStein.L1
