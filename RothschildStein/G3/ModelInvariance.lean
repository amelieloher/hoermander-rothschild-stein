-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelFields
public import Mathlib.Analysis.Calculus.FDeriv.Comp
@[expose] public section
noncomputable section
namespace RothschildStein.G3

private theorem contDiff_left_slice {M : ℕ}
    (f : (Fin M → ℝ) → (Fin M → ℝ) → Fin M → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) (u : Fin M → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (f u) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin M → ℝ => (u, v)) :=
    contDiff_const.prodMk contDiff_id
  exact hf.comp h

/-- Each left translation is smooth (BB p. 529). -/
theorem contDiff_coordinateLeftTranslation {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateProduct e u) :=
  contDiff_left_slice (coordinateProduct e) (contDiff_coordinateProduct e) u

/-- Differentiated associativity proves left invariance of model fields
(BB Proposition 10.54, p. 530). -/
theorem modelField_left_invariant {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (a₀ u v : Fin M → ℝ) :
    fderiv ℝ (coordinateProduct e u) v (modelField e a₀ v) =
      modelField e a₀ (coordinateProduct e u v) := by
  have he : coordinateProduct e (coordinateProduct e u v) =
      coordinateProduct e u ∘ coordinateProduct e v := by
    funext w
    exact coordinateProduct_assoc e u v w
  have hu := (contDiff_coordinateLeftTranslation e u).differentiable (by simp)
  have hv := (contDiff_coordinateLeftTranslation e v).differentiable (by simp)
  rw [modelField, modelField, he, fderiv_comp 0 hu.differentiableAt hv.differentiableAt]
  simp only [coordinateProduct_zero_right, ContinuousLinearMap.comp_apply]

end RothschildStein.G3
