-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HeatEvaluations
public import HeatKernel.Kernel.EvaluationCovariance
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Covariance of continuous representatives

An L² pullback formula and semigroup intertwining determine evaluation covariance
at every point. The corresponding kernel has the squared normalization factor.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (e : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (τ : (Fin n → ℝ) → (Fin n → ℝ)) (hτ : Continuous τ)
    (hmeasure : Measure.QuasiMeasurePreserving τ volume volume) (c : ℝ)
    (hpull : ∀ f, e.symm f =ᵐ[volume] fun x => c * f (τ x))

include hτ hmeasure hpull

/-- Semigroup intertwining and normalized pullback give pointwise evaluation covariance. -/
theorem heatRepresentativeEvaluation_covariance {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hc : c ≠ 0) (hcomm : ∀ f, T s (e.symm f) = e.symm (T t f))
    (x : Fin n → ℝ) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    heatRepresentativeEvaluation T u hu hae t (τ x) f =
      c⁻¹ * heatRepresentativeEvaluation T u hu hae s x (e.symm f) := by
  have hrep : u s (e.symm f) =ᵐ[volume] fun y => c * u t f (τ y) := by
    filter_upwards [hae s hs (e.symm f), hpull (T t f),
      hmeasure.ae_eq_comp (hae t ht f)] with y hy hp ht'
    calc
      u s (e.symm f) y = T s (e.symm f) y := hy.symm
      _ = e.symm (T t f) y := congrArg
        (fun g : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) => g y) (hcomm f)
      _ = c * T t f (τ y) := hp
      _ = c * u t f (τ y) := congrArg (fun z => c * z) ht'
  have heq := Measure.eq_of_ae_eq hrep (hu s hs (e.symm f))
    (continuous_const.mul ((hu t ht f).comp hτ))
  rw [heatRepresentativeEvaluation_apply T u hu hae ht,
    heatRepresentativeEvaluation_apply T u hu hae hs, congrFun heq x,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Normalized pullback and half-time intertwining give kernel covariance everywhere. -/
theorem heatRepresentativeKernel_covariance {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hc : c ≠ 0) (hcomm : ∀ f, T (s / 2) (e.symm f) = e.symm (T (t / 2) f))
    (x y : Fin n → ℝ) :
    evaluationKernel (heatRepresentativeEvaluation T u hu hae) t (τ x) (τ y) =
      (c⁻¹) ^ 2 * evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x y := by
  apply evaluationKernel_covariance_of_evaluations
    (heatRepresentativeEvaluation T u hu hae) e τ c⁻¹ s t
  intro z f
  exact heatRepresentativeEvaluation_covariance T u hu hae e τ hτ hmeasure c hpull
    (half_pos hs) (half_pos ht) hc hcomm z f

end HeatKernel
