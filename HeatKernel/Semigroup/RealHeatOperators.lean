-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.StrongContinuity
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-! # Restriction of heat operators to a real Hilbert subspace

A closed real subspace invariant under the resolvent inherits the heat operators. The
ambient complex realization and invariance are explicit hypotheses.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal

namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Restriction of the heat operator to an invariant closed real subspace. -/
def realHeatOperator (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ≥0) : S →L[ℝ] S :=
  ((heatOperator R t).restrictScalars ℝ).restrict
    (mapsTo_heatOperator_of_mapsTo S hS R hR hinv hspec t)

@[simp] theorem coe_realHeatOperator_apply (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ≥0) (x : S) :
    (realHeatOperator S hS R hR hinv hspec t x : E) = heatOperator R t x := rfl

theorem realHeatOperator_zero (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) :
    realHeatOperator S hS R hR hinv hspec 0 = 1 := by
  ext x
  simpa using congrArg (fun T : E →L[ℂ] E => T (x : E)) (heatOperator_zero R hR)

theorem realHeatOperator_add (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (s t : ℝ≥0) :
    realHeatOperator S hS R hR hinv hspec (s + t) =
      realHeatOperator S hS R hR hinv hspec s * realHeatOperator S hS R hR hinv hspec t := by
  ext x
  simpa only [coe_realHeatOperator_apply, mul_apply_eq_comp] using
    congrArg (fun T : E →L[ℂ] E => T (x : E)) (heatOperator_add R s t)

theorem norm_realHeatOperator_le (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ≥0) :
    ‖realHeatOperator S hS R hR hinv hspec t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖heatOperator R t (x : E)‖ ≤ 1 * ‖(x : E)‖
  exact ((heatOperator R t).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_heatOperator_le R hspec t) (norm_nonneg _))

theorem continuous_realHeatOperator_apply_of_denseRange
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (hdense : DenseRange R) (x : S) :
    Continuous (fun t : ℝ≥0 => realHeatOperator S hS R hR hinv hspec t x) := by
  exact (continuous_heatOperator_apply_of_denseRange R hR hspec hdense (x : E)).subtype_mk _

end HeatKernel
