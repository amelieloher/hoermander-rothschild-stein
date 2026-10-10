-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Local uniform bounds from a comparison map

An injective continuous comparison into a normed space identifies uniform limits of
continuous representatives. The closed graph theorem then bounds every evaluation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace HeatKernel

variable {H F X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X] [CompactSpace X]

/-- A continuous injective comparison identifies limits and closes the representative graph. -/
theorem continuous_of_injective_comparison (L : H →ₗ[ℝ] C(X, ℝ))
    (J : C(X, ℝ) →L[ℝ] F) (B : H →L[ℝ] F) (hJ : Function.Injective J)
    (hcomp : ∀ f, J (L f) = B f) : Continuous L := by
  apply L.continuous_of_seq_closed_graph
  intro u f g hu hg
  apply hJ
  rw [hcomp]
  have h₁ := (J.continuous.tendsto g).comp hg
  have h₂ := (B.continuous.tendsto f).comp hu
  have hseq : (fun n => J (L (u n))) = fun n => B (u n) := funext fun n => hcomp (u n)
  change Tendsto (fun n => J (L (u n))) atTop (𝓝 (J g)) at h₁
  rw [hseq] at h₁
  exact tendsto_nhds_unique h₁ h₂

/-- The closed graph bound is uniform over the compact set of evaluation points. -/
theorem exists_evaluation_bound_of_injective_comparison (L : H →ₗ[ℝ] C(X, ℝ))
    (J : C(X, ℝ) →L[ℝ] F) (B : H →L[ℝ] F) (hJ : Function.Injective J)
    (hcomp : ∀ f, J (L f) = B f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f x, ‖L f x‖ ≤ C * ‖f‖ := by
  let S : H →L[ℝ] C(X, ℝ) :=
    { toLinearMap := L, cont := continuous_of_injective_comparison L J B hJ hcomp }
  exact ⟨‖S‖, norm_nonneg S, fun f x =>
    (ContinuousMap.norm_coe_le_norm (S f) x).trans (S.le_opNorm f)⟩

end HeatKernel
