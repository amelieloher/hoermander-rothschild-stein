-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ParabolicEnergyCurves
public import HeatKernel.Moser.AveragedChainRule

/-! # Time chain rules for cutoff energy curves of weak solutions

Compact time restrictions of the Bochner energy curves extend by zero to global square
integrable curves. Their time averages obey the weighted functional chain rule almost everywhere.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- All differentiable scalar functionals and time weights satisfy the almost-everywhere
chain rule along the forward averages of this curve. -/
def SatisfiesWeightedAverageChainRule {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (w : ℝ → E) : Prop :=
  ∀ (h : ℝ) (Φ : E → ℝ), Differentiable ℝ Φ →
    ∀ χ : ℝ → ℝ, Differentiable ℝ χ →
      ∀ᵐ t ∂volume, HasDerivAt (fun s => χ s * Φ (forwardTimeAverage h w s))
        (deriv χ t * Φ (forwardTimeAverage h w t) + χ t *
          fderiv ℝ Φ (forwardTimeAverage h w t) (h⁻¹ • (w (t + h) - w t))) t

end HeatKernel
