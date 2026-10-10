-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Probability measures defined by conservative kernel rows

A nonnegative integrable row of mass one defines a probability measure by its
density. Integration against this measure is the scalar kernel integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- A nonnegative integrable density of unit mass defines a probability measure. -/
def kernelRowProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : X → ℝ) (hp : Integrable p μ)
    (hnonneg : ∀ x, 0 ≤ p x) (hmass : (∫ x, p x ∂μ) = 1) : ProbabilityMeasure X :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (p x)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hp (Filter.Eventually.of_forall hnonneg),
      hmass, ENNReal.ofReal_one]⟩⟩

/-- Integration against a kernel row probability measure is its scalar density pairing. -/
theorem integral_kernelRowProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : X → ℝ) (hp : Integrable p μ)
    (hnonneg : ∀ x, 0 ≤ p x) (hmass : (∫ x, p x ∂μ) = 1) (f : X → ℝ) :
    (∫ x, f x ∂(kernelRowProbabilityMeasure μ p hp hnonneg hmass : Measure X)) =
      ∫ x, p x * f x ∂μ := by
  change (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (p x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀ hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul]

end HeatKernel
