-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Enlarging the two kernel constants preserves the kernel hypotheses,
allowing the original and transpose bounds to be combined. -/
theorem kernelClass_mono_constants {μ : Measure X} {E : Set X} {β ν A S A' S' : ℝ}
    {K : X → X → ℝ} (H : H2.KernelClass μ E β ν A S K)
    (hA : A ≤ A') (hS : S ≤ S') : H2.KernelClass μ E β ν A' S' K where
  measurable_E := H.measurable_E
  measurable := H.measurable
  β_pos := H.β_pos
  β_le_one := H.β_le_one
  ν_nonneg := H.ν_nonneg
  A_nonneg := H.A_nonneg.trans hA
  S_nonneg := H.S_nonneg.trans hS
  size := by
    intro x hx y hy hxy
    exact (H.size x hx y hy hxy).trans
      (mul_le_mul_of_nonneg_right hA (H2.kernelWeight_nonneg μ ν x y))
  smooth := by
    intro x₀ hx₀ x hx y hy hsep
    exact (H.smooth x₀ hx₀ x hx y hy hsep).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hS (H2.kernelWeight_nonneg μ ν x₀ y))
        (Real.rpow_nonneg (div_nonneg dist_nonneg dist_nonneg) β))

/-- Kernel support and shell identities are unchanged when size and
smoothness bounds are enlarged to common geometric constants. -/
theorem truncatedKernelFacts_mono_constants {μ : Measure X} {A S A' S' : ℝ}
    {K : X → X → ℝ} (H : TruncatedKernelFacts μ A S K)
    (hA : A ≤ A') (hS : S ≤ S') : TruncatedKernelFacts μ A' S' K :=
  ⟨kernelClass_mono_constants H.kernel hA hS, H.support, H.shells⟩

end RothschildStein.H3
