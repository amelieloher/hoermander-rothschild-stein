-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.EvaluationKernel

/-! # Covariance of Riesz evaluations and their kernels

A unitary change of Hilbert-space variables transports bounded evaluations and their
Riesz vectors. Scalar evaluation factors appear squared in the corresponding kernel.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A scaled evaluation identity determines the transformed Riesz vector. -/
theorem evaluationVector_eq_smul_isometry (L M : A → H →L[ℝ] ℝ)
    (e : H ≃ₗᵢ[ℝ] H) (τ : A → A) (a : ℝ)
    (hL : ∀ x f, L (τ x) f = a * M x (e.symm f)) (x : A) :
    evaluationVector L (τ x) = a • e (evaluationVector M x) := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationVector, hL, real_inner_smul_left, e.inner_map_eq_flip,
    inner_evaluationVector]

/-- Unitary evaluation covariance yields the squared scalar factor in kernel covariance. -/
theorem evaluationKernel_covariance_of_evaluations (L : ℝ → A → H →L[ℝ] ℝ)
    (e : H ≃ₗᵢ[ℝ] H) (τ : A → A) (a s t : ℝ)
    (hL : ∀ x f, L (t / 2) (τ x) f = a * L (s / 2) x (e.symm f)) (x y : A) :
    evaluationKernel L t (τ x) (τ y) = a ^ 2 * evaluationKernel L s x y := by
  unfold evaluationKernel
  rw [evaluationVector_eq_smul_isometry _ _ e τ a hL x,
    evaluationVector_eq_smul_isometry _ _ e τ a hL y,
    real_inner_smul_left, real_inner_smul_right, e.inner_map_map]
  ring

end HeatKernel
