-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.IntegralBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- A single absolute dominant controls every input subset. -/
theorem abs_setIntegral_le_of_subset {μ : Measure X} {G H : Set X} {g : X → ℝ}
    (hi : IntegrableOn g G μ) (hHG : H ⊆ G) {C : ℝ} (hC : 0 ≤ C)
    (hb : (∫⁻ y in G, ENNReal.ofReal |g y| ∂μ) ≤ ENNReal.ofReal C) :
    |∫ y in H, g y ∂μ| ≤ C := by
  apply abs_integral_le_of_lintegral (hi.mono_set hHG) hC
  exact (lintegral_mono' (Measure.restrict_mono hHG le_rfl) le_rfl).trans hb

end RothschildStein.H2
