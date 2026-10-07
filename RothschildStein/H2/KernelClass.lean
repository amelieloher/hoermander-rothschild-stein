-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.VolumeComparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The radial weight d(x,y)^ν / V(x;y) from BB (7.6), p. 299.
The total extension is used only off the diagonal in the kernel bounds. -/
def kernelWeight (μ : Measure X) (ν : ℝ) (x y : X) : ℝ :=
  dist x y ^ ν / (volumeAt μ x y).toReal

/-- The two estimates of BB Definition 7.10, p. 299. Smoothness is in the
first variable only. Measurability is on E × E, with no restriction outside E. -/
structure KernelClass (μ : Measure X) (E : Set X) (β ν A S : ℝ)
    (K : X → X → ℝ) : Prop where
  measurable_E : MeasurableSet E
  measurable : Measurable (fun p : E × E => K p.1 p.2)
  β_pos : 0 < β
  β_le_one : β ≤ 1
  ν_nonneg : 0 ≤ ν
  A_nonneg : 0 ≤ A
  S_nonneg : 0 ≤ S
  size : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → |K x y| ≤ A * kernelWeight μ ν x y
  smooth : ∀ x₀ ∈ E, ∀ x ∈ E, ∀ y ∈ E, 2 * dist x₀ x < dist x₀ y →
    |K x₀ y - K x y| ≤ S * kernelWeight μ ν x₀ y * (dist x₀ x / dist x₀ y) ^ β

/-- Radial kernel weights are nonnegative. -/
theorem kernelWeight_nonneg (μ : Measure X) (ν : ℝ) (x y : X) :
    0 ≤ kernelWeight μ ν x y :=
  div_nonneg (Real.rpow_nonneg dist_nonneg _) ENNReal.toReal_nonneg

/-- Decreasing the smoothness exponent retains both constants. -/
theorem KernelClass.of_le {μ : Measure X} {E : Set X} {β β' ν A S : ℝ}
    {K : X → X → ℝ} (hK : KernelClass μ E β ν A S K)
    (hβ' : 0 < β') (hβ : β' ≤ β) : KernelClass μ E β' ν A S K where
  measurable_E := hK.measurable_E
  measurable := hK.measurable
  β_pos := hβ'
  β_le_one := hβ.trans hK.β_le_one
  ν_nonneg := hK.ν_nonneg
  A_nonneg := hK.A_nonneg
  S_nonneg := hK.S_nonneg
  size := hK.size
  smooth := by
    intro x₀ hx₀ x hx y hy hsep
    rcases eq_or_ne x₀ x with rfl | hneq
    · simp [Real.zero_rpow hβ'.ne']
    have hd : 0 < dist x₀ y := by have := dist_nonneg (x := x₀) (y := x); linarith
    have ht : dist x₀ x / dist x₀ y ≤ 1 :=
      (div_le_iff₀ hd).mpr (by have := dist_nonneg (x := x₀) (y := x); linarith)
    exact (hK.smooth x₀ hx₀ x hx y hy hsep).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge
        (div_pos (dist_pos.mpr hneq) hd) ht hβ)
        (mul_nonneg hK.S_nonneg (kernelWeight_nonneg _ _ _ _)))

/-- Sums of singular kernels use the minimum smoothness exponent and
sums of the size and smoothness constants. -/
theorem KernelClass.add {μ : Measure X} {E : Set X} {β₀ β₁ A₀ A₁ S₀ S₁ : ℝ}
    {K₀ K₁ : X → X → ℝ} (h₀ : KernelClass μ E β₀ 0 A₀ S₀ K₀)
    (h₁ : KernelClass μ E β₁ 0 A₁ S₁ K₁) :
    KernelClass μ E (min β₀ β₁) 0 (A₀ + A₁) (S₀ + S₁) (fun x y => K₀ x y + K₁ x y) := by
  have hp : 0 < min β₀ β₁ := lt_min h₀.β_pos h₁.β_pos
  have g₀ := h₀.of_le hp (min_le_left _ _)
  have g₁ := h₁.of_le hp (min_le_right _ _)
  refine ⟨g₀.measurable_E, g₀.measurable.add g₁.measurable, hp, g₀.β_le_one,
    by norm_num, add_nonneg g₀.A_nonneg g₁.A_nonneg, add_nonneg g₀.S_nonneg g₁.S_nonneg, ?_, ?_⟩
  · intro x hx y hy hxy
    calc
      _ ≤ |K₀ x y| + |K₁ x y| := abs_add_le _ _
      _ ≤ A₀ * kernelWeight μ 0 x y + A₁ * kernelWeight μ 0 x y :=
        add_le_add (g₀.size x hx y hy hxy) (g₁.size x hx y hy hxy)
      _ = _ := by ring
  · intro x₀ hx₀ x hx y hy hs
    have he : K₀ x₀ y + K₁ x₀ y - (K₀ x y + K₁ x y) =
        (K₀ x₀ y - K₀ x y) + (K₁ x₀ y - K₁ x y) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add (g₀.smooth x₀ hx₀ x hx y hy hs)
      (g₁.smooth x₀ hx₀ x hx y hy hs)).trans_eq (by ring))

end RothschildStein.H2
