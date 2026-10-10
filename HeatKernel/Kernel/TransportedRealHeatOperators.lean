-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealHeatOperators

/-! # Transport of real heat operators between Hilbert spaces

An isometric identification with a closed real subspace transports its
heat operators and their composition and continuity properties.
-/

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace HeatKernel

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Heat operators transported through a real Hilbert isometry. -/
def transportedRealHeatOperator (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (e : H ≃ₗᵢ[ℝ] S) (t : ℝ≥0) : H →L[ℝ] H :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((realHeatOperator S hS R hR hinv hσ t).comp e.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The identifying isometry intertwines the transported and original real heat operators. -/
theorem apply_transportedRealHeatOperator (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (e : H ≃ₗᵢ[ℝ] S) (t : ℝ≥0) (v : H) :
    e (transportedRealHeatOperator S hS R hR hinv hσ e t v) =
      realHeatOperator S hS R hR hinv hσ t (e v) := e.apply_symm_apply _

end HeatKernel
