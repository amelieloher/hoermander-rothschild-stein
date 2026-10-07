-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
variable {X : Type*} [MetricSpace X]

/-- Case II. A size bound supplies the exponent-one kernel
difference bound in the annulus between separation factors two and four.
This proves the larger-separation repair rather than assuming it. -/
theorem kernel_difference_near_of_size {K : X → X → ℝ} {A e : ℝ}
    (hA : 0 ≤ A) (he : e ≤ 0)
    (hsize : ∀ x y, x ≠ y → |K x y| ≤ A * dist x y ^ e)
    {x₀ x y : X} (hfar : 2 * dist x₀ x < dist x₀ y)
    (hnear : dist x₀ y ≤ 4 * dist x₀ x) :
    |K x₀ y - K x y| ≤
      (4 * A * (1 + (2 : ℝ) ^ (-e))) * dist x₀ x * dist x₀ y ^ (e - 1) := by
  have hρ : 0 < dist x₀ y := by linarith [dist_nonneg (x := x₀) (y := x)]
  have hhalf : dist x₀ y / 2 ≤ dist x y := by
    have ht := dist_triangle x₀ x y
    linarith
  have hxy' : x ≠ y := by
    intro h
    rw [h, dist_self] at hhalf
    linarith
  have hpow : dist x y ^ e ≤ (2 : ℝ) ^ (-e) * dist x₀ y ^ e := by
    have hb := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < dist x₀ y / 2) hhalf he
    have hp : (dist x₀ y / 2) ^ e = (2 : ℝ) ^ (-e) * dist x₀ y ^ e := by
      rw [Real.div_rpow hρ.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    exact hb.trans_eq hp
  have hsum : |K x₀ y - K x y| ≤
      A * (1 + (2 : ℝ) ^ (-e)) * dist x₀ y ^ e := by
    calc
      _ ≤ |K x₀ y| + |K x y| := abs_sub _ _
      _ ≤ A * dist x₀ y ^ e + A * dist x y ^ e :=
        add_le_add (hsize x₀ y (dist_pos.mp hρ)) (hsize x y hxy')
      _ ≤ A * dist x₀ y ^ e + A * ((2 : ℝ) ^ (-e) * dist x₀ y ^ e) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hA)
      _ = _ := by ring
  have hcoef : 0 ≤ A * (1 + (2 : ℝ) ^ (-e)) * dist x₀ y ^ e := by positivity
  have hratio : (1 : ℝ) ≤ 4 * dist x₀ x / dist x₀ y :=
    (le_div_iff₀ hρ).mpr (by simpa using hnear)
  calc
    _ ≤ A * (1 + (2 : ℝ) ^ (-e)) * dist x₀ y ^ e := hsum
    _ ≤ (A * (1 + (2 : ℝ) ^ (-e)) * dist x₀ y ^ e) *
        (4 * dist x₀ x / dist x₀ y) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hcoef
    _ = _ := by rw [Real.rpow_sub_one hρ.ne']; ring

end RothschildStein.H3
