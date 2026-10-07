-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.IntegralDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Data D, with doubled-ball estimates and separate support for both
pieces, for the supported-kernel estimate (BB Proposition 7.17, pp. 306–308). -/
structure LocalKernelData (D : LocDoubling X) (d : TruncDist D) where
  z : X
  center : z ∈ D.Ω₀
  R : ℝ
  radius_pos : 0 < R
  radius_lt : R < D.κ
  R' : ℝ
  support_radius_pos : 0 < R'
  support_radius_le : R' ≤ d.θ₁ * R
  a : X → ℝ
  b : X → ℝ
  Lₐ : ℝ≥0
  Lᵦ : ℝ≥0
  cutoff_a : KernelCutoff (ball z R) Lₐ a
  cutoff_b : KernelCutoff (ball z R) Lᵦ b
  β₀ : ℝ
  β : ℝ
  ν : ℝ
  ν_pos : 0 < ν
  A₀ : ℝ
  S₀ : ℝ
  A₁ : ℝ
  S₁ : ℝ
  K₀ : X → X → ℝ
  K₁ : X → X → ℝ
  singular : KernelClass D.μ (ball z (2 * R)) β₀ 0 A₀ S₀ K₀
  fractional : KernelClass D.μ (ball z (2 * R)) β ν A₁ S₁ K₁
  support₀ : ∀ x ∈ ball z R, ∀ y ∈ ball z (2 * R), R' ≤ d.d' x y → K₀ x y = 0
  support₁ : ∀ x ∈ ball z R, ∀ y ∈ ball z (2 * R), R' ≤ d.d' x y → K₁ x y = 0
  vanishing : ∀ x ∈ ball z R, ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → r₂ ≤ R' →
    ∫ y in ball z (2 * R) ∩ {y | r₁ < d.d' x y ∧ d.d' x y < r₂}, K₀ x y ∂D.μ = 0

/-- The original sum kernel in Data D. -/
def LocalKernelData.sumKernel {D : LocDoubling X} {d : TruncDist D}
    (Q : LocalKernelData D d) (x y : X) : ℝ := Q.K₀ x y + Q.K₁ x y

/-- The localized sum kernel, BB (7.5), p. 299. -/
def LocalKernelData.cutoffKernel {D : LocDoubling X} {d : TruncDist D}
    (Q : LocalKernelData D d) : X → X → ℝ :=
  localizedKernel (ball Q.z Q.R) Q.a Q.b Q.sumKernel

end RothschildStein.H2
