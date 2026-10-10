-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TimeAverageDerivatives

/-! # Almost-everywhere limits of Banach-valued time averages

Differentiation of the indefinite Bochner integral gives convergence of forward averages
at almost every time for locally integrable curves.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Forward time averages of a locally integrable Banach-valued curve converge at almost
 every time in the norm topology. -/
theorem ae_tendsto_forwardTimeAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {u : ℝ → E} (hu : LocallyIntegrable u volume) :
    ∀ᵐ t ∂volume, Tendsto (fun h => forwardTimeAverage h u t) (𝓝[>] 0) (𝓝 (u t)) := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hu] with t ht
  simpa only [forwardTimeAverage, intervalIntegral.integral_same, sub_zero] using
    (ht t).tendsto_slope_zero_right

end HeatKernel
