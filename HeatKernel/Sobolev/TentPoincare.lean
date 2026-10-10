-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LayerPoincare
import Mathlib.Tactic

/-! # Weighted layer bounds for the linear and squared distance tents -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- The squared-tent layer weight has mass three quarters on the inner half interval. -/
theorem lintegral_half_unit_tent :
    (∫⁻ s in Ioo (0 : ℝ) (1 / 2), ENNReal.ofReal (2 * (1 - s))) =
      ENNReal.ofReal (3 / 4 : ℝ) := by
  have hi : IntegrableOn (fun s : ℝ => 2 * (1 - s)) (Ioo 0 (1 / 2)) :=
    (by fun_prop : Continuous (fun s : ℝ => 2 * (1 - s))).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
      change 0 ≤ 2 * (1 - s)
      nlinarith [hs.2]))]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have he : (fun s : ℝ => 2 * (1 - s)) = fun s => 2 - 2 * s := by funext s; ring
  rw [he, intervalIntegral.integral_sub (f := fun _ : ℝ => (2 : ℝ))
    (g := fun s : ℝ => 2 * s) (continuous_const.intervalIntegrable _ _)
    ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, _root_.integral_id, intervalIntegral.integral_const]
  norm_num

/-- The linear distance tent integrates the local layer estimates with coefficient `a + b`. -/
theorem lintegral_tent_mul_le_of_layer_estimates {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : α → ℝ} (hd : Measurable d)
    (hnonneg : ∀ x, 0 ≤ d x) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {a b : ℝ≥0∞}
    (hsmall : ∀ s ∈ Ioo (0 : ℝ) (1 / 2),
      (∫⁻ x in {x | d x < s}, f x ∂μ) ≤ a * ∫⁻ x in {x | d x < 1 / 2}, g x ∂μ)
    (hlarge : ∀ s ∈ Ico (1 / 2 : ℝ) 1,
      (∫⁻ x in {x | d x < s}, f x ∂μ) ≤ b * ∫⁻ x in {x | d x < s}, g x ∂μ) :
    (∫⁻ x, ENNReal.ofReal (max (1 - d x) 0) * f x ∂μ) ≤
      (a + b) * ∫⁻ x, ENNReal.ofReal (max (1 - d x) 0) * g x ∂μ := by
  have hw : ∀ x, d x < 1 / 2 → 1 ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (max (1 - d x) 0) := by
    intro x hx
    have h : (1 : ℝ) ≤ 2 * max (1 - d x) 0 := by nlinarith [le_max_left (1 - d x) 0]
    have H := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at H
    norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at H
    exact H
  have H := lintegral_weighted_le_of_layer_poincare (μ := μ) hd measurable_const
    (by fun_prop : Measurable (fun x => ENNReal.ofReal (max (1 - d x) 0))) hf hg
    (fun x => (lintegral_indicator_layers_eq_tent (hnonneg x)).symm) hw hsmall hlarge
  have hm : (∫⁻ s in Ioo (0 : ℝ) (1 / 2), (1 : ℝ≥0∞)) = (2 : ℝ≥0∞)⁻¹ := by
    calc
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by norm_num [lintegral_const, Real.volume_Ioo]
      _ = _ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [hm] at H
  have he : (2 : ℝ≥0∞)⁻¹ * a * 2 = a := by
    calc
      _ = ((2 : ℝ≥0∞)⁻¹ * 2) * a := by ring
      _ = a := by rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  simpa only [he] using H

/-- The squared distance tent integrates the local layer estimates with coefficient `3a + b`. -/
theorem lintegral_tent_sq_mul_le_of_layer_estimates {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : α → ℝ} (hd : Measurable d)
    (hnonneg : ∀ x, 0 ≤ d x) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {a b : ℝ≥0∞}
    (hsmall : ∀ s ∈ Ioo (0 : ℝ) (1 / 2),
      (∫⁻ x in {x | d x < s}, f x ∂μ) ≤ a * ∫⁻ x in {x | d x < 1 / 2}, g x ∂μ)
    (hlarge : ∀ s ∈ Ico (1 / 2 : ℝ) 1,
      (∫⁻ x in {x | d x < s}, f x ∂μ) ≤ b * ∫⁻ x in {x | d x < s}, g x ∂μ) :
    (∫⁻ x, ENNReal.ofReal (max (1 - d x) 0 ^ 2) * f x ∂μ) ≤
      (3 * a + b) * ∫⁻ x, ENNReal.ofReal (max (1 - d x) 0 ^ 2) * g x ∂μ := by
  have hw : ∀ x, d x < 1 / 2 → 1 ≤ (4 : ℝ≥0∞) * ENNReal.ofReal (max (1 - d x) 0 ^ 2) := by
    intro x hx
    have hm : (1 / 2 : ℝ) ≤ max (1 - d x) 0 := by linarith [le_max_left (1 - d x) 0]
    have h : (1 : ℝ) ≤ 4 * max (1 - d x) 0 ^ 2 := by nlinarith
    have H := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at H
    norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at H
    exact H
  have H := lintegral_weighted_le_of_layer_poincare (μ := μ) hd
    (by fun_prop : Measurable (fun s : ℝ => ENNReal.ofReal (2 * (1 - s))))
    (by fun_prop : Measurable (fun x => ENNReal.ofReal (max (1 - d x) 0 ^ 2))) hf hg
    (fun x => (lintegral_weighted_layers_eq_tent_sq (hnonneg x)).symm) hw hsmall hlarge
  rw [lintegral_half_unit_tent] at H
  have hc : ENNReal.ofReal (3 / 4 : ℝ) * 4 = 3 := by
    calc
      _ = ENNReal.ofReal (3 / 4 : ℝ) * ENNReal.ofReal (4 : ℝ) := by rw [ENNReal.ofReal_ofNat]
      _ = ENNReal.ofReal ((3 / 4 : ℝ) * 4) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ = 3 := by norm_num
  have he : ENNReal.ofReal (3 / 4 : ℝ) * a * 4 = 3 * a := by
    calc
      _ = (ENNReal.ofReal (3 / 4 : ℝ) * 4) * a := by ring
      _ = 3 * a := by rw [hc]
  simpa only [he] using H

end HeatKernel.Sobolev
