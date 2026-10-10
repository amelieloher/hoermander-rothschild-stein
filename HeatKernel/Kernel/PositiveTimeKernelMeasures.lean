-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelProbabilityMeasures

/-! # Positive-time kernel measures and their initial condition

Conservative rows define probability measures at positive times. Extending
by a point mass elsewhere gives a real-time family whose right limit is the
same point mass whenever the scalar bounded-test initial condition holds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology

namespace HeatKernel

/-- Probability measures of positive-time kernel rows, extended by a point mass at other times. -/
def positiveTimeKernelProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ → X → ℝ)
    (hp : ∀ t, 0 < t → Integrable (p t) μ)
    (hnonneg : ∀ t, 0 < t → ∀ y, 0 ≤ p t y)
    (hmass : ∀ t, 0 < t → (∫ y, p t y ∂μ) = 1) (x : X) (t : ℝ) :
    ProbabilityMeasure X :=
  if ht : 0 < t then kernelRowProbabilityMeasure μ (p t) (hp t ht) (hnonneg t ht) (hmass t ht)
  else (Measure.dirac x).toProbabilityMeasure

/-- The bounded continuous initial condition is weak convergence of the positive-time kernel measures to a point mass. -/
theorem tendsto_positiveTimeKernelProbabilityMeasure {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    (μ : Measure X) (p : ℝ → X → ℝ)
    (hp : ∀ t, 0 < t → Integrable (p t) μ)
    (hnonneg : ∀ t, 0 < t → ∀ y, 0 ≤ p t y)
    (hmass : ∀ t, 0 < t → (∫ y, p t y ∂μ) = 1) (x : X)
    (hlimit : ∀ φ : X → ℝ, Continuous φ → (∃ C : ℝ, ∀ y, |φ y| ≤ C) →
      Tendsto (fun t => ∫ y, p t y * φ y ∂μ) (𝓝[>] 0) (𝓝 (φ x))) :
    Tendsto (positiveTimeKernelProbabilityMeasure μ p hp hnonneg hmass x)
      (𝓝[>] 0) (𝓝 ((Measure.dirac x).toProbabilityMeasure)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hdirac : (∫ y, φ y ∂((Measure.dirac x).toProbabilityMeasure : Measure X)) = φ x :=
    integral_dirac' (fun y => φ y) x φ.continuous.stronglyMeasurable
  rw [hdirac]
  have hφ := hlimit φ φ.continuous ⟨‖φ‖, fun y => by
    simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm y⟩
  apply hφ.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  rw [positiveTimeKernelProbabilityMeasure, dite_eq_left htpos, integral_kernelRowProbabilityMeasure]

end HeatKernel
