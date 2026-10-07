-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- The derivative of a horizontal chart with its parameter
retained is an upper triangular equivalence. -/
def upperTriangularDerivativeEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : E ≃L[ℝ] E) (C : F →L[ℝ] E) : (E × F) ≃L[ℝ] (E × F) :=
  ((ContinuousLinearEquiv.prodComm ℝ E F).trans
    ((ContinuousLinearEquiv.refl ℝ F).skewProd H C)).trans
      (ContinuousLinearEquiv.prodComm ℝ F E)

/-- The inverse derivative retains the parameter and inverts the horizontal block. -/
theorem upperTriangularDerivativeEquiv_symm_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : E ≃L[ℝ] E) (C : F →L[ℝ] E) (p : E × F) :
    (upperTriangularDerivativeEquiv H C).symm p = (H.symm (p.1 - C p.2), p.2) := rfl

/-- An invertible horizontal partial derivative makes the derivative
of the parameter-retaining chart invertible on the whole product. -/
theorem upperTriangularDerivativeEquiv_eq_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (E × F) →L[ℝ] E) (H : E ≃L[ℝ] E)
    (hH : L.comp (ContinuousLinearMap.inl ℝ E F) = (H : E →L[ℝ] E)) :
    (upperTriangularDerivativeEquiv H (L.comp (ContinuousLinearMap.inr ℝ E F)) :
      (E × F) →L[ℝ] (E × F)) = L.prod (ContinuousLinearMap.snd ℝ E F) := by
  apply ContinuousLinearMap.ext
  intro p
  have hh := ContinuousLinearMap.coprod_comp_inl_inr L
  rw [hH] at hh
  have he := congrArg (fun A : (E × F) →L[ℝ] E => A p) hh
  exact Prod.ext he rfl

end RothschildStein.L1
