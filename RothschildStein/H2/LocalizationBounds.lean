-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalizedKernelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- A bounded [0,1] cutoff product cannot increase an absolute value. -/
theorem cutoff_product_abs_le {a b k : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) : |a * k * b| ≤ |k| := by
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc
    _ ≤ 1 * |k| * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right ha₁ (abs_nonneg _)) hb₁ hb (by positivity)
    _ = _ := by ring

/-- On a bounded radius, the Lipschitz variation has a Hölder ratio bound.
This is the scalar estimate used in all three nonzero cases of BB pp. 300–301. -/
theorem lipschitz_variation_ratio {a : X → ℝ} {L : ℝ≥0} (ha : LipschitzWith L a)
    {x₀ x y : X} {β R : ℝ} (hβ : 0 < β) (hβ₁ : β ≤ 1)
    (hsep : 2 * dist x₀ x < dist x₀ y) (hrad : dist x₀ y ≤ 4 * R) :
    |a x₀ - a x| ≤ 4 * R * (L : ℝ) * (dist x₀ x / dist x₀ y) ^ β := by
  have hd : 0 < dist x₀ y := by have := dist_nonneg (x := x₀) (y := x); linarith
  have hR : 0 ≤ R := by linarith
  rcases eq_or_ne x₀ x with rfl | hneq
  · simp [Real.zero_rpow hβ.ne']
  have htpos : 0 < dist x₀ x / dist x₀ y := div_pos (dist_pos.mpr hneq) hd
  have htone : dist x₀ x / dist x₀ y ≤ 1 := (div_le_iff₀ hd).mpr (by
    have := dist_nonneg (x := x₀) (y := x); linarith)
  have hpow : dist x₀ x / dist x₀ y ≤ (dist x₀ x / dist x₀ y) ^ β := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge htpos htone hβ₁
  have hdelt : dist x₀ x ≤ 4 * R * (dist x₀ x / dist x₀ y) ^ β := by
    calc
      _ = dist x₀ y * (dist x₀ x / dist x₀ y) := by field_simp
      _ ≤ 4 * R * (dist x₀ x / dist x₀ y) ^ β :=
        mul_le_mul hrad hpow (le_of_lt htpos) (by positivity)
  calc
    _ ≤ (L : ℝ) * dist x₀ x := by simpa [Real.dist_eq] using ha.dist_le_mul x₀ x
    _ ≤ (L : ℝ) * (4 * R * (dist x₀ x / dist x₀ y) ^ β) :=
      mul_le_mul_of_nonneg_left hdelt L.coe_nonneg
    _ = _ := by ring

/-- Two points in the localization ball are less than 2R apart. -/
theorem dist_lt_two_radius {z x y : X} {R : ℝ} (hx : x ∈ ball z R) (hy : y ∈ ball z R) :
    dist x y < 2 * R := by
  have hx' := mem_ball.mp hx
  have hy' := mem_ball.mp hy
  have ht := dist_triangle x z y
  rw [dist_comm z y] at ht
  linarith

end RothschildStein.H2
