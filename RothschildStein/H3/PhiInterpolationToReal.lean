-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalEstimateAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- Finite zero and second Phi values turn the extended interpolation
bound into the real scalar bound required for absorption. -/
theorem phi_interpolation_toReal {P₀ P₁ P₂ : ℝ≥0∞} {δ cE : ℝ}
    (hP₀ : P₀ ≠ ⊤) (hP₂ : P₂ ≠ ⊤) (hδ : 0 < δ) (hcE : 0 ≤ cE)
    (hb : P₁ ≤ ENNReal.ofReal δ * P₂ + ENNReal.ofReal (cE/δ) * P₀) :
    P₁.toReal ≤ δ * P₂.toReal + cE/δ * P₀.toReal := by
  have hfin : ENNReal.ofReal δ * P₂ + ENNReal.ofReal (cE/δ) * P₀ ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfin hb
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
    ENNReal.toReal_ofReal (div_nonneg hcE hδ.le)] using hr

end RothschildStein.H3
