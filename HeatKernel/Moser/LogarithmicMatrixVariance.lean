-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMatrixAbsorption
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Weighted logarithmic variance in uniformly elliptic matrix energy -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A measurable positive quadratic form bounded above by the coordinate-square
energy has an integrable weighted density whenever the weighted gradient moment
is integrable. No matrix-energy integrability assumption is required. -/
theorem integrable_weighted_logarithmic_matrix_energy
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {w : α → ℝ} {d : ι → α → ℝ} {upper : ℝ}
    (hw : AEStronglyMeasurable w μ) (hwn : ∀ᵐ x ∂μ, 0 ≤ w x)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hd : ∀ i, AEStronglyMeasurable (d i) μ)
    (hi : Integrable (fun x => w x * coordinateNormSq (fun i => d i x)) μ)
    (hquad : ∀ᵐ x ∂μ, 0 ≤ matrixEnergy (fun i j => a i j x) (fun i => d i x) ∧
      matrixEnergy (fun i j => a i j x) (fun i => d i x) ≤
        upper * coordinateNormSq (fun i => d i x)) :
    Integrable (fun x => w x * matrixEnergy (fun i j => a i j x) (fun i => d i x)) μ := by
  apply (hi.const_mul upper).mono'
  · exact hw.mul (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => ((ha i j).mul (hd j)).mul (hd i))
  · filter_upwards [hwn, hquad] with x hx hq
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx hq.1)]
    have H := mul_le_mul_of_nonneg_left hq.2 hx
    nlinarith

/-- Uniform ellipticity converts a coordinate-gradient variance bound to a
matrix-energy bound, retaining the reciprocal ellipticity constant. -/
theorem logarithmic_variance_le_matrix_energy
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {w f : α → ℝ} {d : ι → α → ℝ}
    {m K ell upper : ℝ} (hell : 0 < ell) (hK : 0 ≤ K)
    (hw : AEStronglyMeasurable w μ) (hwn : ∀ᵐ x ∂μ, 0 ≤ w x)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hd : ∀ i, AEStronglyMeasurable (d i) μ)
    (hi : Integrable (fun x => w x * coordinateNormSq (fun i => d i x)) μ)
    (hquad : ∀ᵐ x ∂μ,
      ell * coordinateNormSq (fun i => d i x) ≤
        matrixEnergy (fun i j => a i j x) (fun i => d i x) ∧
      matrixEnergy (fun i j => a i j x) (fun i => d i x) ≤
        upper * coordinateNormSq (fun i => d i x))
    (hvariance : (∫ x, w x * (f x - m)^2 ∂μ) ≤
      K * ∫ x, w x * coordinateNormSq (fun i => d i x) ∂μ) :
    Integrable (fun x => w x * matrixEnergy (fun i j => a i j x) (fun i => d i x)) μ ∧
      (∫ x, w x * (f x - m)^2 ∂μ) ≤
        (K / ell) * ∫ x, w x * matrixEnergy (fun i j => a i j x) (fun i => d i x) ∂μ := by
  have hpos : ∀ᵐ x ∂μ, 0 ≤ matrixEnergy (fun i j => a i j x) (fun i => d i x) ∧
      matrixEnergy (fun i j => a i j x) (fun i => d i x) ≤
        upper * coordinateNormSq (fun i => d i x) := by
    filter_upwards [hquad] with x hx
    exact ⟨(mul_nonneg hell.le (Finset.sum_nonneg fun i _ => sq_nonneg (d i x))).trans hx.1, hx.2⟩
  have hj := integrable_weighted_logarithmic_matrix_energy hw hwn ha hd hi hpos
  have H := integral_mono_ae (hi.const_mul ell) hj (show
      (fun x => ell * (w x * coordinateNormSq (fun i => d i x))) ≤ᵐ[μ]
      (fun x => w x * matrixEnergy (fun i j => a i j x) (fun i => d i x)) from by
      filter_upwards [hwn, hquad] with x hx hq
      have H := mul_le_mul_of_nonneg_left hq.1 hx
      nlinarith)
  rw [integral_const_mul] at H
  refine ⟨hj, hvariance.trans ?_⟩
  have H' := mul_le_mul_of_nonneg_left H (div_nonneg hK hell.le)
  calc
    K * (∫ x, w x * coordinateNormSq (fun i => d i x) ∂μ) =
        (K / ell) * (ell * ∫ x, w x * coordinateNormSq (fun i => d i x) ∂μ) := by
          field_simp
    _ ≤ _ := H'

end HeatKernel
