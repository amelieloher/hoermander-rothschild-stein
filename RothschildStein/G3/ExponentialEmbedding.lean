-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteAnalytic
public import RothschildStein.G3.ModelInvariance
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Continuous coordinate inclusion into the finite associative algebra
(BB Proposition 10.54, p. 530). -/
def coordinateInclusionCL {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    (Fin M → ℝ) →L[ℝ] FiniteWordAlgebra a s p :=
  LinearMap.toContinuousLinearMap (coordinateInclusion e)

/-- Continuous coordinate retraction from the finite associative algebra
(BB Proposition 10.54, p. 530). -/
def coordinateRetractionCL {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    FiniteWordAlgebra a s p →L[ℝ] (Fin M → ℝ) :=
  LinearMap.toContinuousLinearMap (coordinateRetraction e)

/-- Polynomial exponential embedding of model coordinates into the
associative coefficient algebra (BB pp. 528–531). -/
def modelExp {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : FiniteWordAlgebra a s p :=
  finiteExp (coordinateInclusionCL e u)

/-- A global polynomial left inverse of the model exponential embedding
(BB pp. 475–476, 528–531). -/
def modelLog {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (f : FiniteWordAlgebra a s p) : Fin M → ℝ :=
  coordinateRetractionCL e (logApprox (f - 1) s)

/-- Smoothness of the exponential embedding (BB p. 530). -/
theorem contDiff_modelExp {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    ContDiff ℝ (⊤ : ℕ∞) (modelExp e) :=
  contDiff_finiteExp.comp (coordinateInclusionCL e).contDiff

/-- Smoothness of the polynomial left inverse (BB p. 530). -/
theorem contDiff_modelLog {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    ContDiff ℝ (⊤ : ℕ∞) (modelLog e) :=
  (coordinateRetractionCL e).contDiff.comp
    ((contDiff_logApprox s).comp (contDiff_id.sub contDiff_const))

/-- The logarithm retracts the exponential embedding (BB pp. 475–476). -/
theorem modelLog_modelExp {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u : Fin M → ℝ) : modelLog e (modelExp e u) = u := by
  change coordinateRetractionCL e (logApprox (finiteExp (coordinateInclusionCL e u) - 1) s) = u
  have hp : FiniteOrderAtLeast 1 (coordinateInclusionCL e u) :=
    formalSpan_positive_order (e u).val (e u).property
  rw [logApprox_finiteExp hp]
  exact (coordinateRetraction_apply e (e u)).trans (e.symm_apply_apply u)

/-- The exponential differential at the identity is the coordinate
inclusion (BB pp. 530–531). -/
theorem hasFDerivAt_modelExp_zero {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) :
    HasFDerivAt (modelExp e) (coordinateInclusionCL e) 0 := by
  have hE : HasFDerivAt (finiteExp (a := a) (s := s) (p := p))
      (ContinuousLinearMap.id ℝ _) (coordinateInclusionCL e 0) := by
    rw [map_zero]
    exact hasFDerivAt_finiteExp_zero
  have h := hE.comp 0 (coordinateInclusionCL e).hasFDerivAt
  rw [ContinuousLinearMap.id_comp] at h
  exact h

/-- The exponential embedding preserves model multiplication
(BB (9.76), p. 470; Proposition 10.52, p. 529). -/
theorem modelExp_product {a s M : ℕ} {p : Fin a → ℕ+}
    (e : (Fin M → ℝ) ≃ₗ[ℝ] formalSpan a s p) (u v : Fin M → ℝ) :
    modelExp e (coordinateProduct e u v) = modelExp e u * modelExp e v := by
  change finiteExp (e (coordinateProduct e u v)).val = finiteExp (e u).val * finiteExp (e v).val
  rw [coordinateProduct_map]
  exact finiteExp_BCH (formalSpan_positive_order (e u).val (e u).property)
    (formalSpan_positive_order (e v).val (e v).property)
end RothschildStein.G3
