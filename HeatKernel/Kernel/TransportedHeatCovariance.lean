-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TransportedRealHeatOperators

/-! # Heat covariance under compatible real and complex actions -/

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace HeatKernel

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The ambient realization of a transported real heat operator is the complex heat operator. -/
theorem coe_apply_transportedRealHeatOperator
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (e : H ≃ₗᵢ[ℝ] S) (t : ℝ≥0) (f : H) :
    (e (transportedRealHeatOperator S hS R hR hinv hσ e t f) : E) =
      heatOperator R t (e f : E) := by
  rw [apply_transportedRealHeatOperator, coe_realHeatOperator_apply]

/-- Compatible real and complex actions transport ambient heat covariance to the real heat family. -/
theorem transportedRealHeatOperator_unitary_of_ambient_covariance
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hσ : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (e : H ≃ₗᵢ[ℝ] S)
    (U : H ≃ₗᵢ[ℝ] H) (W : E ≃ₗᵢ[ℂ] E)
    (hW : ∀ f, W (e f : E) = (e (U f) : E)) (c t : ℝ≥0)
    (hcov : ∀ v, heatOperator R t (W v) = W (heatOperator R (c * t) v)) (f : H) :
    transportedRealHeatOperator S hS R hR hinv hσ e t (U f) =
      U (transportedRealHeatOperator S hS R hR hinv hσ e (c * t) f) := by
  apply e.injective
  apply Subtype.coe_injective
  calc
    (e (transportedRealHeatOperator S hS R hR hinv hσ e t (U f)) : E) =
        heatOperator R t (e (U f) : E) := coe_apply_transportedRealHeatOperator S hS R hR hinv hσ e t _
    _ = heatOperator R t (W (e f : E)) := congrArg (heatOperator R t) (hW f).symm
    _ = W (heatOperator R (c * t) (e f : E)) := hcov _
    _ = W (e (transportedRealHeatOperator S hS R hR hinv hσ e (c * t) f) : E) :=
      congrArg W (coe_apply_transportedRealHeatOperator S hS R hR hinv hσ e (c * t) f).symm
    _ = (e (U (transportedRealHeatOperator S hS R hR hinv hσ e (c * t) f)) : E) := hW _

end HeatKernel
