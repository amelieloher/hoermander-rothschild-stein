-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelWords
public import RothschildStein.G3.FreeModels
public import RothschildStein.G3.ModelFlows
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- The bounded nested words selected by the homogeneous basis
(BB Theorems 10.31–10.32, pp. 511–512). -/
def modelBasisWord {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (j : Fin (freeDimension a s p)) : List (Fin a) :=
  (D.basis_commutator j).choose

/-- The selected words are nonempty, bounded, and represent the basis
(BB Proposition 10.48, p. 525). -/
theorem modelBasisWord_spec {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (j : Fin (freeDimension a s p)) :
    modelBasisWord D j ≠ [] ∧ wordWeight p (modelBasisWord D j) ≤ s ∧
      (D.basis j).val = truncatedBracket (modelBasisWord D j) :=
  (D.basis_commutator j).choose_spec

/-- The coordinate weight is exactly the selected word's weight
(BB Remark 10.51, p. 528). -/
theorem modelBasisWord_weight {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (j : Fin (freeDimension a s p)) : wordWeight p (modelBasisWord D j) = D.weight j := by
  have he := D.basis_homogeneous j
  rw [(modelBasisWord_spec D j).2.2, weightProjection_truncatedBracket] at he
  by_contra h
  rw [ite_eq_right h] at he
  have hz : D.basis j = 0 := Subtype.ext ((modelBasisWord_spec D j).2.2.trans he.symm)
  exact D.basis.ne_zero j hz

/-- The selected word has exactly its canonical coordinate vector
(BB (10.59), p. 531). -/
theorem wordCoordinates_modelBasisWord {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (j : Fin (freeDimension a s p)) :
    wordCoordinates D.basis.equivFun.symm (modelBasisWord D j) =
      Hormander.Interface.basisVec j := by
  have he : wordLieElement (modelBasisWord D j) = D.basis j :=
    Subtype.ext (modelBasisWord_spec D j).2.2.symm
  rw [wordCoordinates, he]
  ext k
  simp only [LinearEquiv.symm_symm, Module.Basis.equivFun_self,
    Hormander.Interface.basisVec, Pi.single_apply, eq_comm]

/-- The chosen word fields form the canonical basis at the identity
(BB Theorems 10.31–10.32, pp. 511–512). -/
theorem modelBasisWord_origin {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (j : Fin (freeDimension a s p)) :
    wordBracket (modelGenerators D.basis.equivFun.symm) (modelBasisWord D j) 0 =
      Hormander.Interface.basisVec j := by
  rw [wordBracket_modelGenerators, modelField_zero, wordCoordinates_modelBasisWord]

/-- Exact radial cancellation for the selected word frame
(BB Proposition 10.55, p. 532). -/
theorem modelBasisWord_radial {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (u : Fin (freeDimension a s p) → ℝ) :
    ∑ j, u j • wordBracket (modelGenerators D.basis.equivFun.symm)
      (modelBasisWord D j) u = u := by
  simp only [wordBracket_modelGenerators, wordCoordinates_modelBasisWord, modelField,
    ← map_smul, ← map_sum]
  have hu : (∑ j, u j • Hormander.Interface.basisVec j) = u := by
    ext k
    simp [Hormander.Interface.basisVec, Pi.single_apply]
  rw [hu]
  exact modelField_radial D.basis.equivFun.symm u
end RothschildStein.G3
