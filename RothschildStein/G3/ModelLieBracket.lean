-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelExpDifferential
public import Mathlib.Analysis.Calculus.VectorField
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The coefficient Lie bracket expressed in model coordinates
(BB Proposition 10.54, pp. 530–531). -/
def coordinateLieBracket {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v w : Fin M → ℝ) : Fin M → ℝ :=
  let c : FiniteWordAlgebra a s p := ⁅coordinateInclusionCL e v, coordinateInclusionCL e w⁆
  e.symm ⟨c, finiteLieSpan_lie_mem (e v).property (e w).property⟩

/-- Coordinate inclusion preserves the coefficient Lie bracket
(BB p. 531). -/
theorem coordinateInclusionCL_lieBracket {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v w : Fin M → ℝ) :
    coordinateInclusionCL e (coordinateLieBracket e v w) =
      ⁅coordinateInclusionCL e v, coordinateInclusionCL e w⁆ :=
  congrArg Subtype.val (e.apply_symm_apply _)

/-- Exponentiation pushes the bracket of model fields to the associative
commutator field. The symmetric second derivative cancels by the vector-field
chain rule (BB (10.56)–(10.57), pp. 530–531). -/
theorem modelExp_push_lieBracket {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v w u : Fin M → ℝ) :
    fderiv ℝ (modelExp e) u (VectorField.lieBracket ℝ (modelField e v) (modelField e w) u) =
      modelExp e u * ⁅coordinateInclusionCL e v, coordinateInclusionCL e w⁆ := by
  have hf := (contDiff_modelExp e).differentiable (by simp)
  have hv := (contDiff_modelField e v).differentiable (by simp)
  have hw := (contDiff_modelField e w).differentiable (by simp)
  have h := VectorField.fderiv_apply_lieBracket ((contDiff_modelExp e).contDiffAt (x := u))
    (by simp) (hw.differentiableAt (x := u)) (hv.differentiableAt (x := u))
  have heV : (fun x => fderiv ℝ (modelExp e) x (modelField e v x)) =
      finiteMulCL.flip (coordinateInclusionCL e v) ∘ modelExp e := by
    funext x
    exact modelExp_push_modelField e v x
  have heW : (fun x => fderiv ℝ (modelExp e) x (modelField e w x)) =
      finiteMulCL.flip (coordinateInclusionCL e w) ∘ modelExp e := by
    funext x
    exact modelExp_push_modelField e w x
  rw [heW, heV] at h
  have hdV := ((finiteMulCL.flip (coordinateInclusionCL e v)).hasFDerivAt.comp u
    hf.differentiableAt.hasFDerivAt).fderiv
  have hdW := ((finiteMulCL.flip (coordinateInclusionCL e w)).hasFDerivAt.comp u
    hf.differentiableAt.hasFDerivAt).fderiv
  rw [hdW, hdV] at h
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [modelExp_push_modelField, modelExp_push_modelField] at h
  change fderiv ℝ (modelExp e) u
    (VectorField.lieBracket ℝ (modelField e v) (modelField e w) u) =
    (modelExp e u * coordinateInclusionCL e v) * coordinateInclusionCL e w -
      (modelExp e u * coordinateInclusionCL e w) * coordinateInclusionCL e v at h
  rw [h, Ring.lie_def, mul_sub, mul_assoc, mul_assoc]

/-- The model-field assignment preserves Lie brackets everywhere
(BB Proposition 10.54, pp. 530–531). -/
theorem modelField_lieBracket {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v w u : Fin M → ℝ) :
    VectorField.lieBracket ℝ (modelField e v) (modelField e w) u =
      modelField e (coordinateLieBracket e v w) u := by
  apply modelExp_fderiv_injective e u
  rw [modelExp_push_lieBracket, modelExp_push_modelField, coordinateInclusionCL_lieBracket]
end RothschildStein.G3
