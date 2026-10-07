-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A bounded-support fractional kernel is singular, with the two
explicit radius factors in this estimate (BB Definition 7.10, p. 299). -/
theorem KernelClass.singular_of_support {μ : Measure X} {E : Set X} {β ν A S R : ℝ}
    {K : X → X → ℝ} (hK : KernelClass μ E β ν A S K) (hR : 0 < R)
    (hsupp : ∀ x ∈ E, ∀ y ∈ E, R ≤ dist x y → K x y = 0) :
    KernelClass μ E β 0 (A * R ^ ν) (S * (2 * R) ^ ν) K := by
  refine ⟨hK.measurable_E, hK.measurable, hK.β_pos, hK.β_le_one, le_rfl,
    mul_nonneg hK.A_nonneg (Real.rpow_nonneg hR.le _),
    mul_nonneg hK.S_nonneg (Real.rpow_nonneg (by positivity) _), ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hr : R ≤ dist x y
    · rw [hsupp x hx y hy hr, abs_zero]
      exact mul_nonneg (mul_nonneg hK.A_nonneg (Real.rpow_nonneg hR.le _))
        (kernelWeight_nonneg μ 0 x y)
    · calc
        _ ≤ A * kernelWeight μ ν x y := hK.size x hx y hy hxy
        _ ≤ _ := by
          rw [kernelWeight_eq_mul]
          have hp := Real.rpow_le_rpow dist_nonneg (le_of_not_ge hr) hK.ν_nonneg
          have he := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp hK.A_nonneg) (kernelWeight_nonneg μ 0 x y)
          nlinarith
  · intro x₀ hx₀ x hx y hy hsep
    by_cases hz : K x₀ y - K x y = 0
    · rw [hz, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hK.S_nonneg
        (Real.rpow_nonneg (by positivity) _)) (kernelWeight_nonneg μ 0 x₀ y))
        (Real.rpow_nonneg (by positivity) _)
    · have hr : dist x₀ y ≤ 2 * R := by
        by_contra hn
        have hd₀ : R ≤ dist x₀ y := by linarith
        have hd : R ≤ dist x y := by
          have := (distance_comparison hsep).2
          linarith
        exact hz (by rw [hsupp x₀ hx₀ y hy hd₀, hsupp x hx y hy hd]; ring)
      calc
        _ ≤ S * kernelWeight μ ν x₀ y * (dist x₀ x / dist x₀ y) ^ β :=
          hK.smooth x₀ hx₀ x hx y hy hsep
        _ ≤ _ := by
          rw [kernelWeight_eq_mul]
          have hp := Real.rpow_le_rpow dist_nonneg hr hK.ν_nonneg
          have hw := kernelWeight_nonneg μ 0 x₀ y
          have ht : 0 ≤ (dist x₀ x / dist x₀ y) ^ β := Real.rpow_nonneg (by positivity) _
          calc
            _ = dist x₀ y ^ ν * (S * kernelWeight μ 0 x₀ y *
              (dist x₀ x / dist x₀ y) ^ β) := by ring
            _ ≤ (2 * R) ^ ν * (S * kernelWeight μ 0 x₀ y *
              (dist x₀ x / dist x₀ y) ^ β) :=
                mul_le_mul_of_nonneg_right hp (mul_nonneg (mul_nonneg hK.S_nonneg hw) ht)
            _ = _ := by ring

end RothschildStein.H2
