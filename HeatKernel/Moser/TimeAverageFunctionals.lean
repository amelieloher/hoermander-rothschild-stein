-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TimeAverageDerivatives

/-! # Continuous linear tests of locally integrable time averages

Energy-space curves need only local Bochner integrability. Continuous linear tests commute
with their one-sided averages and give scalar difference-quotient derivatives almost everywhere.
-/

@[expose] public section

open MeasureTheory

namespace HeatKernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Continuous linear maps commute with forward averages of locally integrable curves. -/
theorem map_forwardTimeAverage_of_locallyIntegrable (L : E →L[ℝ] F) {u : ℝ → E}
    (hu : LocallyIntegrable u volume) (h t : ℝ) :
    L (forwardTimeAverage h u t) = forwardTimeAverage h (L ∘ u) t := by
  have hi : IntervalIntegrable u volume t (t + h) :=
    (hu.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  simp only [forwardTimeAverage, map_smul]
  congr 1
  simpa only [Function.comp_def] using (L.intervalIntegral_comp_comm hi).symm

omit [CompleteSpace F]

/-- Linear tests of a forward average have the tested forward difference quotient as derivative. -/
theorem ae_hasDerivAt_map_forwardTimeAverage (L : E →L[ℝ] F) {u : ℝ → E}
    (hu : LocallyIntegrable u volume) (h : ℝ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun s => L (forwardTimeAverage h u s))
      (h⁻¹ • (L (u (t + h)) - L (u t))) t := by
  filter_upwards [ae_hasDerivAt_forwardTimeAverage hu h] with t ht
  simpa only [map_smul, map_sub, Function.comp_def] using L.hasFDerivAt.comp_hasDerivAt t ht

end HeatKernel
