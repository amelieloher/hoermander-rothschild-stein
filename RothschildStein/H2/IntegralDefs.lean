-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelLocalization
public import RothschildStein.H2.VolumeIntegrals
public import RothschildStein.H2.HolderEstimates
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- BB (7.10), p. 301: subtraction regularizes the singular kernel. -/
def regularizedIntegral (μ : Measure X) (G : Set X) (K : X → X → ℝ)
    (f : X → ℝ) (x : X) : ℝ := ∫ y in G, K x y * (f y - f x) ∂μ

/-- BB (7.10), p. 301: the open truncation used in the singular integral. -/
def truncatedIntegral (μ : Measure X) (G : Set X) (d' K : X → X → ℝ)
    (ε : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  ∫ y in G ∩ {y | ε < d' x y}, K x y * f y ∂μ

/-- The absolutely convergent fractional integral, BB (7.13), p. 305. -/
def fractionalIntegral (μ : Measure X) (G : Set X) (K : X → X → ℝ)
    (f : X → ℝ) (x : X) : ℝ := ∫ y in G, K x y * f y ∂μ

/-- Kernel support in the input domain, with centers restricted to E.
This records the kernel support condition and the inclusions E ⊆ G ⊆ Ω₁. -/
structure SupportedKernel (D : LocDoubling X) (E G : Set X) (β ν A S R : ℝ)
    (K : X → X → ℝ) : Prop where
  measurable_E : MeasurableSet E
  sub_EG : E ⊆ G
  sub_G : G ⊆ D.Ω₁
  radius_pos : 0 < R
  radius_le : R ≤ 3 * D.κ
  kernel : KernelClass D.μ G β ν A S K
  support : ∀ x ∈ E, ∀ y ∈ G, R ≤ dist x y → K x y = 0

/-- Open-shell cancellation, including the endpoint condition.
BB (7.11), p. 301; the shells are strictly open. -/
def ShellCancellation (μ : Measure X) (E G : Set X) (d' K : X → X → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ x ∈ E, ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ →
    |∫ y in G ∩ {y | r₁ < d' x y ∧ d' x y < r₂}, K x y ∂μ| ≤ C

/-- The explicit principal-value formula after T(1) has been identified. The limit theorem certifies this formula directly. -/
def pvFormula (μ : Measure X) (G : Set X) (K : X → X → ℝ) (h f : X → ℝ) (x : X) : ℝ :=
  regularizedIntegral μ G K f x + h x * f x

end RothschildStein.H2
