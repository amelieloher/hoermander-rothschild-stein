-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelInvariance
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The model product is addition along each fixed Lie direction
(BB Proposition 10.55, p. 531). -/
theorem coordinateProduct_collinear {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v : Fin M → ℝ) (r t : ℝ) :
    coordinateProduct e (r • v) (t • v) = (r + t) • v := by
  apply e.injective
  apply Subtype.ext
  rw [coordinateProduct_map, map_smul, map_smul, map_smul]
  change finiteBCH (r • (e v).val) (t • (e v).val) = (r + t) • (e v).val
  let f : FiniteWordAlgebra a s p := (e v).val
  have hp : FiniteOrderAtLeast 1 f := formalSpan_positive_order (e v).val (e v).property
  have hc : Commute f f := rfl
  have hrt : Commute (r • f) (t • f) := (hc.smul_left r).smul_right t
  exact (finiteBCH_eq_add_of_commute (finiteOrderAtLeast_smul hp r)
    (finiteOrderAtLeast_smul hp t) hrt).trans (add_smul r t f).symm

/-- The model field is constant on its own scalar line
(BB Proposition 10.55, p. 531). -/
theorem modelField_collinear {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (v : Fin M → ℝ) (t : ℝ) :
    modelField e v (t • v) = v := by
  have he : (fun h : ℝ => coordinateProduct e (t • v) (h • v)) =
      (fun h : ℝ => (t + h) • v) := funext (coordinateProduct_collinear e v t)
  have hp := (contDiff_coordinateLeftTranslation e (t • v)).differentiable (by simp)
  have hv := (hasDerivAt_id (0 : ℝ)).smul_const v
  have hleft := hp.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hv
  simp only [id_eq, Function.comp_def, zero_smul, one_smul] at hleft
  rw [he] at hleft
  have hright := ((hasDerivAt_const (0 : ℝ) t).add (hasDerivAt_id (0 : ℝ))).smul_const v
  simpa only [zero_add, one_smul, modelField] using hleft.unique hright

/-- Radial cancellation as a pointwise vector identity
(BB Proposition 10.55, pp. 531–532). -/
theorem modelField_radial {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : modelField e u u = u := by
  simpa only [one_smul] using modelField_collinear e u 1

end RothschildStein.G3
