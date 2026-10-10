-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Weighted squared distance to constants

The normalized weighted mean minimizes the quadratic integral. The moment
hypotheses make the statement applicable without a probability normalization.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {w u : α → ℝ}

/-- The mean of a function with respect to a real weight. -/
noncomputable def weightedMean (μ : Measure α) (w u : α → ℝ) : ℝ :=
  (∫ x, w x * u x ∂μ) / (∫ x, w x ∂μ)

/-- Integrability of squared distance follows from the three weighted moments. -/
theorem integrable_weight_mul_sub_sq
    (hw : Integrable w μ) (hwu : Integrable (fun x => w x * u x) μ)
    (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ) (c : ℝ) :
    Integrable (fun x => w x * (u x - c) ^ 2) μ := by
  convert (hwu₂.sub (hwu.mul_const (2 * c))).add (hw.mul_const (c ^ 2)) using 1
  ext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Expansion of the quadratic integral into its three moments. -/
theorem integral_weight_mul_sub_sq
    (hw : Integrable w μ) (hwu : Integrable (fun x => w x * u x) μ)
    (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ) (c : ℝ) :
    (∫ x, w x * (u x - c) ^ 2 ∂μ) =
      (∫ x, w x * u x ^ 2 ∂μ) - (∫ x, w x * u x ∂μ) * (2 * c) +
        (∫ x, w x ∂μ) * c ^ 2 := by
  have hpoly : (fun x => w x * (u x - c) ^ 2) =
      (fun x => w x * u x ^ 2 - w x * u x * (2 * c) + w x * c ^ 2) := by
    funext x
    ring
  rw [hpoly]
  have hsub : Integrable (fun x => w x * u x ^ 2 - w x * u x * (2 * c)) μ :=
    hwu₂.sub (hwu.mul_const _)
  rw [integral_add hsub (hw.mul_const _),
    integral_sub hwu₂ (hwu.mul_const _), integral_mul_const, integral_mul_const]

/-- The exact squared-distance decomposition around the normalized weighted mean. -/
theorem integral_weight_mul_sub_sq_eq
    (hw : Integrable w μ) (hwu : Integrable (fun x => w x * u x) μ)
    (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ)
    (hmass : (∫ x, w x ∂μ) ≠ 0) (c : ℝ) :
    (∫ x, w x * (u x - c) ^ 2 ∂μ) =
      (∫ x, w x * (u x - weightedMean μ w u) ^ 2 ∂μ) +
        (∫ x, w x ∂μ) * (weightedMean μ w u - c) ^ 2 := by
  rw [integral_weight_mul_sub_sq hw hwu hwu₂,
    integral_weight_mul_sub_sq hw hwu hwu₂]
  unfold weightedMean
  field_simp [hmass]
  ring

/-- A nonnegative weight's normalized mean minimizes weighted squared distance. -/
theorem integral_weight_mul_sub_weightedMean_sq_le
    (hw : Integrable w μ) (hwu : Integrable (fun x => w x * u x) μ)
    (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ)
    (hmass : 0 < ∫ x, w x ∂μ) (c : ℝ) :
    (∫ x, w x * (u x - weightedMean μ w u) ^ 2 ∂μ) ≤
      ∫ x, w x * (u x - c) ^ 2 ∂μ := by
  rw [integral_weight_mul_sub_sq_eq hw hwu hwu₂ (ne_of_gt hmass) c]
  exact le_add_of_nonneg_right (mul_nonneg hmass.le (sq_nonneg _))

/-- Finite mass and a finite quadratic moment give an integrable first moment. -/
theorem integrable_weight_mul_of_integrable_weight_mul_sq
    (hw : Integrable w μ) (hu : AEStronglyMeasurable u μ)
    (hw₀ : 0 ≤ᵐ[μ] w) (hwu₂ : Integrable (fun x => w x * u x ^ 2) μ) :
    Integrable (fun x => w x * u x) μ := by
  apply (hw.add hwu₂).mono' (hw.aestronglyMeasurable.mul hu)
  filter_upwards [hw₀] with x hx
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx, Pi.add_apply]
  have habs : |u x| ≤ 1 + u x ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
  nlinarith [mul_le_mul_of_nonneg_left habs hx]

end HeatKernel.Sobolev
