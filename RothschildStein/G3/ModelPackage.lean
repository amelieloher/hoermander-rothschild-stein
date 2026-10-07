-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelBasisWords
public import RothschildStein.G3.ModelSpanning
public import RothschildStein.G3.WordHomogeneity
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import RothschildStein.G2.TriangularPolynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import RothschildStein.G2.WeightedPolynomial
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The generators accompanying a concrete homogeneous free group
(BB Theorems 10.31–10.32, pp. 511–512). -/
def FreeModelData.fields {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p) :=
  modelGenerators D.basis.equivFun.symm

/-- The fixed group product agrees with the BCH coordinate product
(BB Proposition 10.52, pp. 528–529). -/
theorem freeModel_mul {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (u v : Fin (freeDimension a s p) → ℝ) :
    D.group.mul u v = coordinateProduct D.basis.equivFun.symm u v :=
  polynomialProduct_coordinateProductPolynomial _ u v

/-- All constructed generator fields are smooth (BB pp. 511–512). -/
theorem freeModel_fields_smooth {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i : Fin a) : ContDiff ℝ (⊤ : ℕ∞) (D.fields i) :=
  contDiff_modelField _ _

/-- Freedom holds at every point of the constructed model
(BB Theorems 10.31–10.32, pp. 511–512). -/
theorem freeModel_fields_freeAt {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (u : Fin (freeDimension a s p) → ℝ) :
    FreeAt p s D.fields u := freeAt_modelGenerators _ u

/-- The model fields are left invariant for the fixed group product
(BB pp. 511–512). -/
theorem freeModel_fields_leftInvariant {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i : Fin a) (u v : Fin (freeDimension a s p) → ℝ) :
    fderiv ℝ (D.group.mul u) v (D.fields i v) = D.fields i (D.group.mul u v) := by
  have he : D.group.mul u = coordinateProduct D.basis.equivFun.symm u :=
    funext (freeModel_mul D u)
  rw [he]
  exact modelField_left_invariant _ _ u v

/-- The inverse in the constructed fixed group is negation
(BB pp. 511–512). -/
theorem freeModel_inv {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (u : Fin (freeDimension a s p) → ℝ) :
    D.group.inv u = -u := by
  ext j
  simp [HomogeneousGroup.inv, FreeModelData.group, homogeneousModelOfBasis]

end RothschildStein.G3
