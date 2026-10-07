-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExponentialEmbedding
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The polynomial exponential embedding has injective differential at
every point, by its polynomial left inverse (BB Proposition 10.54, p. 530). -/
theorem modelExp_fderiv_injective {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    Function.Injective (fderiv ℝ (modelExp e) u) := by
  have hf := (contDiff_modelExp e).differentiable (by simp)
  have hg := (contDiff_modelLog e).differentiable (by simp)
  have he : modelLog e ∘ modelExp e = id := funext (modelLog_modelExp e)
  have h := hg.differentiableAt.hasFDerivAt.comp u hf.differentiableAt.hasFDerivAt
  rw [he] at h
  have hd : (fderiv ℝ (modelLog e) (modelExp e u)).comp (fderiv ℝ (modelExp e) u) =
      ContinuousLinearMap.id ℝ (Fin M → ℝ) := by
    rw [← h.fderiv, fderiv_id]
  have hl : Function.LeftInverse (fderiv ℝ (modelLog e) (modelExp e u))
      (fderiv ℝ (modelExp e) u) := by
    intro v
    exact congrArg (fun T : (Fin M → ℝ) →L[ℝ] (Fin M → ℝ) => T v) hd
  exact hl.injective

/-- Under exponentiation, the model field becomes associative left
multiplication by its origin value (BB (10.56)–(10.57), pp. 530–531). -/
theorem modelExp_push_modelField {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v u : Fin M → ℝ) :
    fderiv ℝ (modelExp e) u (modelField e v u) =
      modelExp e u * coordinateInclusionCL e v := by
  have hp := (contDiff_coordinateLeftTranslation e u).differentiable (by simp)
  have hf := (contDiff_modelExp e).differentiable (by simp)
  have hL := hf.differentiableAt.hasFDerivAt.comp 0 hp.differentiableAt.hasFDerivAt
  have hR := (finiteMulCL (modelExp e u)).hasFDerivAt.comp 0 (hasFDerivAt_modelExp_zero e)
  have he : modelExp e ∘ coordinateProduct e u = finiteMulCL (modelExp e u) ∘ modelExp e := by
    funext w
    exact modelExp_product e u w
  rw [he] at hL
  have hd := hL.unique hR
  simp only [coordinateProduct_zero_right] at hd
  have h := congrArg (fun T : (Fin M → ℝ) →L[ℝ] FiniteWordAlgebra a s p => T v) hd
  simpa only [ContinuousLinearMap.comp_apply, finiteMulCL_apply, modelField] using h
end RothschildStein.G3
