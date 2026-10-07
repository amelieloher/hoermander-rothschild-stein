-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CoordinatePolynomials
public import RothschildStein.G2.PolynomialCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The coordinate model product is jointly smooth (BB p. 529). -/
theorem contDiff_coordinateProduct {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : (Fin M → ℝ) × (Fin M → ℝ) => coordinateProduct e z.1 z.2) := by
  have he : (fun z : (Fin M → ℝ) × (Fin M → ℝ) => coordinateProduct e z.1 z.2) =
      (fun z => polynomialProduct (coordinateProductPolynomial e) z.1 z.2) := by
    funext z
    exact (polynomialProduct_coordinateProductPolynomial e z.1 z.2).symm
  rw [he]
  apply contDiff_pi.mpr
  intro j
  exact (G2.contDiff_eval (coordinateProductPolynomial e j)).comp
    (contDiff_pi.mpr fun i => Sum.casesOn i
      (fun k => (contDiff_apply ℝ ℝ k).comp contDiff_fst)
      (fun k => (contDiff_apply ℝ ℝ k).comp contDiff_snd))

/-- A model field specified by its value at the origin
(BB Proposition 10.54, pp. 530–531). -/
def modelField {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v u : Fin M → ℝ) : Fin M → ℝ :=
  fderiv ℝ (coordinateProduct e u) 0 v

/-- Model fields are smooth (BB p. 530). -/
theorem contDiff_modelField {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v : Fin M → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelField e v) :=
  (contDiff_coordinateProduct e).fderiv_apply contDiff_const contDiff_const (by simp)

/-- The model field has its prescribed value at zero (BB p. 530). -/
@[simp] theorem modelField_zero {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v : Fin M → ℝ) : modelField e v 0 = v := by
  have he : coordinateProduct e 0 = id := funext (coordinateProduct_zero_left e)
  rw [modelField, he, fderiv_id]
  rfl

/-- Scalar linearity of model fields (BB p. 530). -/
theorem modelField_smul {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (r : ℝ) (v u : Fin M → ℝ) :
    modelField e (r • v) u = r • modelField e v u :=
  map_smul (fderiv ℝ (coordinateProduct e u) 0) r v
end RothschildStein.G3
