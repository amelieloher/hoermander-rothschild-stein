-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateMeasure

/-! # Inverse time-space changes of variables

The inverse time-space coordinate map preserves volume and transports
local integrability from coordinate vectors to time-space products.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- The inverse time-space coordinate equivalence preserves volume. -/
theorem measurePreserving_inverse_timeSpaceCoordinates (n : ℕ) :
    MeasurePreserving (timeSpaceCoordinates n).symm :=
  (measurePreserving_timeSpaceCoordinates n).symm
    (timeSpaceCoordinates n).toHomeomorph.toMeasurableEquiv

/-- Inverse time-space substitution transports local integrability. -/
theorem locallyIntegrableOn_comp_inverse_timeSpaceCoordinates (n : ℕ)
    {s : Set (Fin (1 + n) → ℝ)} (hs : IsOpen s) {f : (Fin (1 + n) → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f s volume) :
    LocallyIntegrableOn (f ∘ (timeSpaceCoordinates n).symm)
      ((timeSpaceCoordinates n).symm ⁻¹' s) volume :=
  locallyIntegrableOn_comp_homeomorph (timeSpaceCoordinates n).symm.toHomeomorph
    (measurePreserving_inverse_timeSpaceCoordinates n) hs hf

end HeatKernel
