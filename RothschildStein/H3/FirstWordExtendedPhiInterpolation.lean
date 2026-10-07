-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FirstWordInverseRadiusInterpolation
public import RothschildStein.H3.PhiInterpolationToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- Extended Phi interpolation and the exact half-radius lower
bound imply the uniform real first-word estimate; finiteness is internal. -/
theorem firstWord_bound_of_extendedPhi_interpolation
    {R D C₂ cE U : ℝ} {P₀ P₁ P₂ : ℝ≥0∞}
    (hR : 0 < R) (hD : 0 ≤ D) (hC₂ : 0 ≤ C₂) (hcE : 0 ≤ cE) (hU : 0 ≤ U)
    (hhalf : ENNReal.ofReal ((R / 2) * D) ≤ P₁)
    (hinterp : P₁ ≤ ENNReal.ofReal R⁻¹ * P₂ + ENNReal.ofReal (cE / R⁻¹) * P₀)
    (hsecond : P₂ ≤ ENNReal.ofReal ((R ^ 2 / 4) * C₂))
    (hzero : P₀ ≤ ENNReal.ofReal U) : D ≤ C₂ / 2 + 2 * cE * U := by
  have hP₀ : P₀ ≠ ∞ := (hzero.trans_lt ENNReal.ofReal_lt_top).ne
  have hP₂ : P₂ ≠ ∞ := (hsecond.trans_lt ENNReal.ofReal_lt_top).ne
  have hright : ENNReal.ofReal R⁻¹ * P₂ + ENNReal.ofReal (cE / R⁻¹) * P₀ ≠ ∞ := by
    finiteness
  have hP₁ : P₁ ≠ ∞ := (hinterp.trans_lt (lt_top_iff_ne_top.mpr hright)).ne
  have hhalf' := ENNReal.toReal_mono hP₁ hhalf
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (R / 2) * D)] at hhalf'
  have hsecond' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsecond
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (R ^ 2 / 4) * C₂)] at hsecond'
  have hzero' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hzero
  rw [ENNReal.toReal_ofReal hU] at hzero'
  exact firstWord_bound_of_inverseRadius_interpolation hR hcE hhalf'
    (phi_interpolation_toReal hP₀ hP₂ (inv_pos.mpr hR) hcE hinterp) hsecond' hzero'

end RothschildStein.H3
