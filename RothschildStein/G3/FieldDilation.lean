-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.HomogeneousModel
public import RothschildStein.G3.ModelInvariance
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted coordinate dilation as a continuous linear map
(BB p. 528). -/
def coordinateDilationCL {M : ℕ} (w : Fin M → ℕ) (t : ℝ) :
    (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) :=
  ContinuousLinearMap.pi fun j => t ^ w j • ContinuousLinearMap.proj j

/-- Differentiated dilation covariance of model fields
(BB Theorems 10.31–10.32 and Proposition 10.54, pp. 511–512, 530–531). -/
theorem modelField_dilation_covariance {a s M : ℕ} {p : Fin a → ℕ+}
    (b : Module.Basis (Fin M) ℝ (formalSpan a s p)) (w : Fin M → ℕ)
    (hw : ∀ j, weightProjection (w j) (b j).val = (b j).val)
    (t : ℝ) (v u : Fin M → ℝ) :
    coordinateDilation w t (modelField b.equivFun.symm v u) =
      modelField b.equivFun.symm (coordinateDilation w t v) (coordinateDilation w t u) := by
  let e := b.equivFun.symm
  let D := coordinateDilationCL w t
  have hp := (contDiff_coordinateLeftTranslation e u).differentiable (by simp)
  have hq := (contDiff_coordinateLeftTranslation e (D u)).differentiable (by simp)
  have hL := D.hasFDerivAt.comp 0 (hp.differentiableAt (x := 0)).hasFDerivAt
  have hR := (hq.differentiableAt (x := D 0)).hasFDerivAt.comp 0 D.hasFDerivAt
  have he : D ∘ coordinateProduct e u = coordinateProduct e (D u) ∘ D := by
    funext x
    exact coordinateDilation_product b w hw t u x
  rw [he] at hL
  have hd := hL.unique hR
  simp only [map_zero] at hd
  have h := congrArg (fun T : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) => T v) hd
  exact h
end RothschildStein.G3
