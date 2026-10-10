-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TimeAverageDerivatives

/-! # Chain rules for one-sided time averages

Locally Bochner-integrable curves have differentiable one-sided averages almost everywhere.
Differentiable energy functionals and time weights can therefore be composed with these averages.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A differentiable functional of a forward average obeys the chain rule almost everywhere. -/
theorem ae_hasDerivAt_comp_forwardTimeAverage {u : ℝ → E}
    (hu : LocallyIntegrable u volume) (h : ℝ) {Φ : E → ℝ}
    (hΦ : Differentiable ℝ Φ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun s => Φ (forwardTimeAverage h u s))
      (fderiv ℝ Φ (forwardTimeAverage h u t) (h⁻¹ • (u (t + h) - u t))) t := by
  filter_upwards [ae_hasDerivAt_forwardTimeAverage hu h] with t ht
  simpa only [Function.comp_def] using (hΦ _).hasFDerivAt.comp_hasDerivAt t ht

/-- A time weight adds its product-rule term to a forward-average chain rule. -/
theorem ae_hasDerivAt_weighted_comp_forwardTimeAverage {u : ℝ → E}
    (hu : LocallyIntegrable u volume) (h : ℝ) {Φ : E → ℝ}
    (hΦ : Differentiable ℝ Φ) {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun s => χ s * Φ (forwardTimeAverage h u s))
      (deriv χ t * Φ (forwardTimeAverage h u t) + χ t *
        fderiv ℝ Φ (forwardTimeAverage h u t) (h⁻¹ • (u (t + h) - u t))) t := by
  filter_upwards [ae_hasDerivAt_comp_forwardTimeAverage hu h hΦ] with t ht
  exact (hχ t).hasDerivAt.mul ht

end HeatKernel
