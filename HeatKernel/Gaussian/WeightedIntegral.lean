-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.MeanValueIntegral
import Mathlib.Tactic

/-! # Local integrals controlled by exponential energy

A lower bound for the weight on a measurable region transfers global weighted
energy to the unweighted local integral used in a mean-value estimate.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set
namespace HeatKernel.Gaussian

/-- A lower bound for the logarithmic weight controls the local integral by
its global weighted energy. -/
theorem integral_le_exp_mul_weighted_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S) {f ψ : α → ℝ} {L : ℝ}
    (hf : IntegrableOn f S μ)
    (hw : Integrable (fun x ↦ Real.exp (ψ x) * f x) μ)
    (hn : ∀ x, 0 ≤ f x) (hψ : ∀ x ∈ S, L ≤ ψ x) :
    (∫ x in S, f x ∂μ) ≤ Real.exp (-L) * ∫ x, Real.exp (ψ x) * f x ∂μ := by
  have hlocal : Real.exp L * (∫ x in S, f x ∂μ) ≤
      ∫ x in S, Real.exp (ψ x) * f x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hf.const_mul _) hw.integrableOn
    exact ae_restrict_of_forall_mem hS (fun x hx ↦
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hψ x hx)) (hn x))
  have hglobal := setIntegral_le_integral (s := S) hw
    (Filter.Eventually.of_forall (fun x ↦ mul_nonneg (Real.exp_pos _).le (hn x)))
  have H := mul_le_mul_of_nonneg_left (hlocal.trans hglobal) (Real.exp_pos (-L)).le
  have he : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
  simpa only [← mul_assoc, he, one_mul] using H

/-- A weighted energy bound on every time slice and an endpoint mean-value
estimate give the first row estimate with its full exponential loss. -/
theorem sq_le_of_weighted_energy_mean_value {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {S : Set α} (hS : MeasurableSet S)
    (v : ℝ → α → ℝ) (ψ : α → ℝ) {s r β ρ t C V p : ℝ}
    (hr : 0 < r) (hV : 0 < V)
    (hψ : ∀ x ∈ S, 2 * β * (ρ - 2 * r) ≤ ψ x)
    (hlocal : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
      IntegrableOn (fun x ↦ v σ x ^ 2) S μ)
    (hweighted : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
      Integrable (fun x ↦ Real.exp (ψ x) * v σ x ^ 2) μ)
    (henergy : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
      (∫ x, Real.exp (ψ x) * v σ x ^ 2 ∂μ) ≤ Real.exp (6 * β ^ 2 * t + 4 * β * r))
    (htime : IntegrableOn (fun σ ↦ ∫ x in S, v σ x ^ 2 ∂μ)
      (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)))
    (hmean : p ^ 2 ≤ C ^ 2 / (r ^ 2 * V) *
      ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), ∫ x in S, v σ x ^ 2 ∂μ) :
    p ^ 2 ≤ 4 * C ^ 2 / V * Real.exp (-2 * β * ρ + 8 * β * r + 6 * β ^ 2 * t) := by
  apply sq_le_of_endpoint_mean_value hr hV htime ?_ hmean
  intro σ hσ
  calc
    _ ≤ Real.exp (-(2 * β * (ρ - 2 * r))) *
        ∫ x, Real.exp (ψ x) * v σ x ^ 2 ∂μ :=
      integral_le_exp_mul_weighted_integral μ hS (hlocal σ hσ) (hweighted σ hσ)
        (fun x ↦ sq_nonneg _) hψ
    _ ≤ Real.exp (-(2 * β * (ρ - 2 * r))) *
        Real.exp (6 * β ^ 2 * t + 4 * β * r) :=
      mul_le_mul_of_nonneg_left (henergy σ hσ) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end HeatKernel.Gaussian
