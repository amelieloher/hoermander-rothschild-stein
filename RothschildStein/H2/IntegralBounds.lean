-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Convert an absolute Lebesgue bound to a Bochner integral bound. -/
theorem abs_integral_le_of_lintegral {μ : Measure X} {g : X → ℝ}
    (hi : Integrable g μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : (∫⁻ y, ENNReal.ofReal |g y| ∂μ) ≤ ENNReal.ofReal C) :
    |∫ y, g y ∂μ| ≤ C := by
  have he : ∫ y, |g y| ∂μ ≤ C := by
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    simpa only [← Real.norm_eq_abs, ← ofReal_norm, ofReal_integral_norm_eq_lintegral_enorm hi] using hb
  calc
    _ ≤ ∫ y, |g y| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) g
    _ ≤ C := he

end RothschildStein.H2
