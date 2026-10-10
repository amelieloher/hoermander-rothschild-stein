-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Spatial tails from weighted quadratic oscillation -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace HeatKernel

/-- A positive lower bound for the weight on a tail set converts weighted variance
into a quadratic measure estimate. All variance and weight assumptions are explicit. -/
theorem measureReal_tail_le_weighted_variance {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {A : Set α} (hA : MeasurableSet A)
    {w f : α → ℝ} {m r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hi : Integrable (fun x => w x * (f x - m)^2) μ)
    (htail : ∀ᵐ x ∂μ, x ∈ A → κ ≤ w x ∧ r ≤ |f x - m|) :
    μ.real A ≤ (∫ x, w x * (f x - m)^2 ∂μ) / (κ * r^2) := by
  have hpoint : ∀ᵐ x ∂μ.restrict A, κ * r^2 ≤ w x * (f x - m)^2 := by
    filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae htail] with x hx ht
    obtain ⟨hk, hd⟩ := ht hx
    have hs : r^2 ≤ (f x - m)^2 := by
      nlinarith [sq_abs (f x - m), abs_nonneg (f x - m)]
    exact (mul_le_mul_of_nonneg_left hs hκ.le).trans
      (mul_le_mul_of_nonneg_right hk (sq_nonneg _))
  have hfirst := integral_mono_ae (integrable_const (κ * r^2))
    (hi.mono_measure μ.restrict_le_self) hpoint
  have hsecond := integral_mono_measure (show μ.restrict A ≤ μ from μ.restrict_le_self)
    (show 0 ≤ᵐ[μ] (fun x => w x * (f x - m)^2) from by
      filter_upwards [hw] with x hx
      exact mul_nonneg hx (sq_nonneg _)) hi
  have hmass : κ * r^2 * μ.real A ≤ ∫ x, w x * (f x - m)^2 ∂μ := by
    simpa only [integral_const, smul_eq_mul, Measure.restrict_apply_univ,
      measureReal_def, mul_comm] using hfirst.trans hsecond
  exact (le_div_iff₀ (mul_pos hκ (sq_pos_of_pos hr))).mpr (by
    simpa only [mul_comm] using hmass)

/-- For a squared distance tent bounded below by one eighty-first, a weighted
Poincaré bound gives the spatial logarithmic-tail majorant. -/
theorem measureReal_tail_le_of_tent_variance {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {A : Set α} (hA : MeasurableSet A)
    {w f : α → ℝ} {m r K E : ℝ} (hr : 0 < r)
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hi : Integrable (fun x => w x * (f x - m)^2) μ)
    (htail : ∀ᵐ x ∂μ, x ∈ A → (1 : ℝ) / 81 ≤ w x ∧ r ≤ |f x - m|)
    (hvariance : (∫ x, w x * (f x - m)^2 ∂μ) ≤ K * E) :
    μ.real A ≤ 81 * K * E / r^2 := by
  have h := measureReal_tail_le_weighted_variance hA hr
    (show (0 : ℝ) < 1 / 81 by norm_num) hw hi htail
  calc
    μ.real A ≤ (K * E) / ((1 / 81) * r^2) :=
      h.trans (div_le_div_of_nonneg_right hvariance (by positivity))
    _ = 81 * K * E / r^2 := by ring

end HeatKernel
