-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.LocalL2Evaluation

/-! # Linearity and bounded evaluation of continuous representatives

Positive measure on open sets makes continuous representatives unique. Agreement with
a linear L² map therefore gives linearity, and the compact-space closed graph argument
gives bounded evaluations.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]

/-- Continuous representatives of a linear L² map form a linear map. -/
def continuousRepresentativeLinearMap (B : H →ₗ[ℝ] Lp ℝ 2 μ) (u : H → X → ℝ)
    (hu : ∀ f, Continuous (u f)) (hae : ∀ f, B f =ᵐ[μ] u f) : H →ₗ[ℝ] C(X, ℝ) where
  toFun f := ⟨u f, hu f⟩
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    have hsum : B (f + g) =ᵐ[μ] (fun y => u f y + u g y) := by
      rw [map_add]
      exact (Lp.coeFn_add (B f) (B g)).trans ((hae f).add (hae g))
    exact congrFun (Measure.eq_of_ae_eq ((hae (f + g)).symm.trans hsum)
      (hu (f + g)) ((hu f).add (hu g))) x
  map_smul' a f := by
    apply ContinuousMap.ext
    intro x
    have hsmul : B (a • f) =ᵐ[μ] (fun y => a • u f y) := by
      rw [map_smul]
      filter_upwards [Lp.coeFn_smul a (B f), hae f] with y hy hf
      rw [hy, Pi.smul_apply, hf]
    exact congrFun (Measure.eq_of_ae_eq ((hae (a • f)).symm.trans hsmul)
      (hu (a • f)) ((hu f).const_smul a)) x

variable [CompleteSpace H] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ]

/-- Continuous L² representatives have uniformly bounded evaluation on the compact space. -/
theorem exists_uniform_bound_continuous_representatives (B : H →L[ℝ] Lp ℝ 2 μ)
    (u : H → X → ℝ) (hu : ∀ f, Continuous (u f)) (hae : ∀ f, B f =ᵐ[μ] u f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f x, ‖u f x‖ ≤ C * ‖f‖ :=
  exists_evaluation_bound_of_localL2_representatives μ
    (continuousRepresentativeLinearMap μ B.toLinearMap u hu hae) B hae

end HeatKernel
