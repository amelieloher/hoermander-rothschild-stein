-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelWords
public import RothschildStein.G3.FieldDilation
public import RothschildStein.G3.FreeModels
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Every model word coordinate is a dilation eigenvector of its actual
weighted word length (BB (10.53), p. 526). -/
theorem wordCoordinates_dilation {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (t : ℝ) (I : List (Fin a)) :
    coordinateDilation D.weight t (wordCoordinates D.basis.equivFun.symm I) =
      t ^ wordWeight p I • wordCoordinates D.basis.equivFun.symm I := by
  apply D.basis.equivFun.symm.injective
  apply Subtype.ext
  rw [basis_coordinateDilation D.basis D.weight D.basis_homogeneous]
  simp only [wordCoordinates, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply,
    Submodule.coe_smul, wordLieElement]
  exact finiteDilate_truncatedBracket t I

/-- Word fields have the reciprocal dilation degree of their weighted
commutator length (BB Theorems 10.31–10.32, pp. 511–512). -/
theorem modelWordField_homogeneous {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (I : List (Fin a)) (t : ℝ) (ht : t ≠ 0)
    (u : Fin (freeDimension a s p) → ℝ) :
    modelField D.basis.equivFun.symm (wordCoordinates D.basis.equivFun.symm I)
      (coordinateDilation D.weight t u) =
    (t ^ wordWeight p I)⁻¹ • coordinateDilation D.weight t
      (modelField D.basis.equivFun.symm (wordCoordinates D.basis.equivFun.symm I) u) := by
  have h := modelField_dilation_covariance D.basis D.weight D.basis_homogeneous t
    (wordCoordinates D.basis.equivFun.symm I) u
  rw [wordCoordinates_dilation, modelField_smul] at h
  have he := congrArg (fun v : Fin (freeDimension a s p) → ℝ => (t ^ wordWeight p I)⁻¹ • v) h
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul] at he
  exact he.symm

/-- Original model generators have the prescribed alphabet degrees,
including degree two for the drift (BB Theorems 10.31–10.32). -/
theorem modelGenerators_homogeneous {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i : Fin a) (t : ℝ) (ht : t ≠ 0)
    (u : Fin (freeDimension a s p) → ℝ) :
    modelGenerators D.basis.equivFun.symm i (coordinateDilation D.weight t u) =
      (t ^ (p i : ℕ))⁻¹ • coordinateDilation D.weight t
        (modelGenerators D.basis.equivFun.symm i u) := by
  simpa only [modelGenerators, wordWeight, List.map_singleton, List.sum_singleton] using
    modelWordField_homogeneous D [i] t ht u
end RothschildStein.G3
