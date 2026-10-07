-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalKernelSetting

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Kernel size and smoothness constants scale by the absolute value
of the scalar. This is the normalization step in BB pp. 357–359. -/
theorem kernelClass_scale {μ : Measure X} {E : Set X} {β ν A S : ℝ}
    {K : X → X → ℝ} (H : H2.KernelClass μ E β ν A S K) (c : ℝ) :
    H2.KernelClass μ E β ν (|c| * A) (|c| * S) (fun x y => c * K x y) where
  measurable_E := H.measurable_E
  measurable := measurable_const.mul H.measurable
  β_pos := H.β_pos
  β_le_one := H.β_le_one
  ν_nonneg := H.ν_nonneg
  A_nonneg := mul_nonneg (abs_nonneg c) H.A_nonneg
  S_nonneg := mul_nonneg (abs_nonneg c) H.S_nonneg
  size := by
    intro x hx y hy hxy
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (H.size x hx y hy hxy) (abs_nonneg c)).trans_eq
      (by ring)
  smooth := by
    intro x₀ hx₀ x hx y hy hsep
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_left (H.smooth x₀ hx₀ x hx y hy hsep)
      (abs_nonneg c)).trans_eq (by ring)

/-- Scaling preserves support and exact shell cancellation as well
as the analytic kernel bounds. -/
theorem truncatedKernelFacts_scale {μ : Measure X} {A S : ℝ} {K : X → X → ℝ}
    (H : TruncatedKernelFacts μ A S K) (c : ℝ) :
    TruncatedKernelFacts μ (|c| * A) (|c| * S) (fun x y => c * K x y) where
  kernel := kernelClass_scale H.kernel c
  support := by
    intro x y hxy
    rw [H.support x y hxy, mul_zero]
  shells := by
    intro x a b ha hab
    rw [integral_const_mul, H.shells x a b ha hab, mul_zero]

/-- Dividing by a positive kernel seminorm removes it from both kernel
bounds without changing any analytic hypothesis. -/
theorem truncatedKernelFacts_normalize {μ : Measure X} {A S Λ : ℝ}
    {K : X → X → ℝ} (hΛ : 0 < Λ)
    (H : TruncatedKernelFacts μ (Λ * A) (Λ * S) K) :
    TruncatedKernelFacts μ A S (fun x y => Λ⁻¹ * K x y) := by
  have hA : |Λ⁻¹| * (Λ * A) = A := by
    rw [abs_of_pos (inv_pos.mpr hΛ), ← mul_assoc, inv_mul_cancel₀ hΛ.ne', one_mul]
  have hS : |Λ⁻¹| * (Λ * S) = S := by
    rw [abs_of_pos (inv_pos.mpr hΛ), ← mul_assoc, inv_mul_cancel₀ hΛ.ne', one_mul]
  simpa only [hA, hS] using truncatedKernelFacts_scale H Λ⁻¹

/-- The zero kernel realizes every pair of nonnegative bounds.
It supplies a kernel-independent numerical reference Data D. -/
theorem truncatedKernelFacts_zero (μ : Measure X) {A S : ℝ}
    (hA : 0 ≤ A) (hS : 0 ≤ S) : TruncatedKernelFacts μ A S (fun _ _ => 0) where
  kernel := {
    measurable_E := MeasurableSet.univ
    measurable := measurable_const
    β_pos := zero_lt_one
    β_le_one := le_rfl
    ν_nonneg := le_rfl
    A_nonneg := hA
    S_nonneg := hS
    size := by
      intro x _ y _ _
      simpa using mul_nonneg hA (H2.kernelWeight_nonneg μ 0 x y)
    smooth := by
      intro x₀ _ x _ y _ _
      simpa using mul_nonneg (mul_nonneg hS (H2.kernelWeight_nonneg μ 0 x₀ y))
        (Real.rpow_nonneg (div_nonneg dist_nonneg dist_nonneg) 1) }
  support := fun _ _ _ => rfl
  shells := by intro x a b _ _; simp

end RothschildStein.H3
