-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

private theorem kernelWeight_order_relation (μ : Measure X) (α v : ℝ)
    {x y : X} (hxy : 0 < dist x y) :
    H2.kernelWeight μ α x y = dist x y ^ (α - v) * H2.kernelWeight μ v x y := by
  unfold H2.kernelWeight
  have he : α = (α - v) + v := by ring
  conv_lhs => rw [he, Real.rpow_add hxy]
  rw [mul_div_assoc]

/-- A cutoff kernel of order α has every lower order v, with the exact
R^(α-v) size factor and (2R)^(α-v) smoothness factor. -/
theorem kernelClass_lower_order_of_support {μ : Measure X} {E : Set X}
    {β α v A S R : ℝ} {K : X → X → ℝ}
    (H : H2.KernelClass μ E β α A S K) (hv : 0 ≤ v) (hvα : v ≤ α)
    (hR : 0 < R) (hsupp : ∀ x y, R < dist x y → K x y = 0) :
    H2.KernelClass μ E β v (A * R ^ (α - v)) (S * (2 * R) ^ (α - v)) K := by
  have hd : 0 ≤ α - v := sub_nonneg.mpr hvα
  refine ⟨H.measurable_E, H.measurable, H.β_pos, H.β_le_one, hv,
    mul_nonneg H.A_nonneg (Real.rpow_nonneg hR.le _),
    mul_nonneg H.S_nonneg (Real.rpow_nonneg (by positivity) _), ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hk : K x y = 0
    · rw [hk, abs_zero]
      exact mul_nonneg (mul_nonneg H.A_nonneg (Real.rpow_nonneg hR.le _))
        (H2.kernelWeight_nonneg μ v x y)
    have hxR : dist x y ≤ R := le_of_not_gt (fun hr => hk (hsupp x y hr))
    have hp := Real.rpow_le_rpow dist_nonneg hxR hd
    calc
      _ ≤ A * H2.kernelWeight μ α x y := H.size x hx y hy hxy
      _ = (A * dist x y ^ (α - v)) * H2.kernelWeight μ v x y := by
        rw [kernelWeight_order_relation μ α v (dist_pos.mpr hxy)]
        ring
      _ ≤ (A * R ^ (α - v)) * H2.kernelWeight μ v x y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp H.A_nonneg)
          (H2.kernelWeight_nonneg μ v x y)
  · intro x₀ hx₀ x hx y hy hsep
    by_cases heq : K x₀ y = K x y
    · rw [heq, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg
        (mul_nonneg H.S_nonneg (Real.rpow_nonneg (by positivity) _))
        (H2.kernelWeight_nonneg μ v x₀ y))
        (Real.rpow_nonneg (div_nonneg dist_nonneg dist_nonneg) _)
    have hρ : 0 < dist x₀ y := by linarith [dist_nonneg (x := x₀) (y := x)]
    have hρR : dist x₀ y ≤ 2 * R := by
      by_cases hzero : K x₀ y = 0
      · have hk : K x y ≠ 0 := by intro hz; exact heq (hzero.trans hz.symm)
        have hxR : dist x y ≤ R := le_of_not_gt (fun hr => hk (hsupp x y hr))
        linarith [dist_triangle x₀ x y]
      · have hxR : dist x₀ y ≤ R := le_of_not_gt (fun hr => hzero (hsupp x₀ y hr))
        linarith
    have hp := Real.rpow_le_rpow hρ.le hρR hd
    have hw : 0 ≤ H2.kernelWeight μ v x₀ y := H2.kernelWeight_nonneg μ v x₀ y
    have hratio : 0 ≤ (dist x₀ x / dist x₀ y) ^ β :=
      Real.rpow_nonneg (div_nonneg dist_nonneg dist_nonneg) _
    calc
      _ ≤ S * H2.kernelWeight μ α x₀ y * (dist x₀ x / dist x₀ y) ^ β :=
        H.smooth x₀ hx₀ x hx y hy hsep
      _ = ((S * dist x₀ y ^ (α - v)) * H2.kernelWeight μ v x₀ y) *
          (dist x₀ x / dist x₀ y) ^ β := by
        rw [kernelWeight_order_relation μ α v hρ]
        ring
      _ ≤ ((S * (2 * R) ^ (α - v)) * H2.kernelWeight μ v x₀ y) *
          (dist x₀ x / dist x₀ y) ^ β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp H.S_nonneg) hw) hratio

end RothschildStein.H3
