-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalizedKernels

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The exact local-doubling setting of BB Proposition 7.11, pp. 299–301.
The proof also includes exponent zero. -/
theorem localized_kernelClass (D : LocDoubling X) {z : X} (hz : z ∈ D.Ω₀)
    {R : ℝ} (hR : 0 < R) (hRκ : R < D.κ)
    {a b : X → ℝ} {Lₐ Lᵦ : ℝ≥0} {K : X → X → ℝ} {β ν A S : ℝ}
    (ha : KernelCutoff (ball z R) Lₐ a) (hb : KernelCutoff (ball z R) Lᵦ b)
    (hK : KernelClass D.μ (ball z R) β ν A S K) :
    KernelClass D.μ D.Ω₁ β ν A
      (S + 4 * R * (Lₐ : ℝ) * D.C_D ^ 2 * (3 / 2 : ℝ) ^ ν * A)
      (localizedKernel (ball z R) a b K) := by
  exact localized_kernelClass_on_patch D.outerPatch D.open₁.measurableSet hR hRκ.le
    ((ball_subset_ball (by have := D.κ_pos; linarith)).trans
      (ball_subset_closedBall.trans (D.incl₀ z hz))) ha hb hK

/-- Singular-kernel specialization with exactly S + 4RLₐC_D²A. -/
theorem localized_singular_kernelClass (D : LocDoubling X) {z : X} (hz : z ∈ D.Ω₀)
    {R : ℝ} (hR : 0 < R) (hRκ : R < D.κ)
    {a b : X → ℝ} {Lₐ Lᵦ : ℝ≥0} {K : X → X → ℝ} {β A S : ℝ}
    (ha : KernelCutoff (ball z R) Lₐ a) (hb : KernelCutoff (ball z R) Lᵦ b)
    (hK : KernelClass D.μ (ball z R) β 0 A S K) :
    KernelClass D.μ D.Ω₁ β 0 A (S + 4 * R * (Lₐ : ℝ) * D.C_D ^ 2 * A)
      (localizedKernel (ball z R) a b K) := by
  simpa only [Real.rpow_zero, mul_one] using localized_kernelClass D hz hR hRκ ha hb hK

end RothschildStein.H2
