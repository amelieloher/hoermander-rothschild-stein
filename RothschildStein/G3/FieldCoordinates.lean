-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelInvariance
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The model field at any point determines its origin value
(BB Proposition 10.54, p. 530). -/
theorem modelField_eq_zero_iff {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v u : Fin M → ℝ) :
    modelField e v u = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have h := modelField_left_invariant e v (-u) u
    rw [hv, map_zero, coordinateProduct_neg_left, modelField_zero] at h
    exact h.symm
  · rintro rfl
    exact map_zero (fderiv ℝ (coordinateProduct e u) 0)

/-- Origin-to-point field evaluation is injective (BB p. 530). -/
theorem modelFieldAt_injective {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    Function.Injective (fun v => modelField e v u) := by
  intro v w hvw
  have hzero : modelField e (v - w) u = 0 := by
    change (fderiv ℝ (coordinateProduct e u) 0) (v - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hvw
  exact sub_eq_zero.mp ((modelField_eq_zero_iff e (v - w) u).mp hzero)

/-- Origin-to-point field evaluation is a linear isomorphism
(BB Proposition 10.54, p. 530). -/
def modelFieldAtEquiv {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) :
    (Fin M → ℝ) ≃ₗ[ℝ] (Fin M → ℝ) :=
  LinearEquiv.ofBijective (fderiv ℝ (coordinateProduct e u) 0).toLinearMap
    ⟨modelFieldAt_injective e u, LinearMap.injective_iff_surjective.mp (modelFieldAt_injective e u)⟩

end RothschildStein.G3
