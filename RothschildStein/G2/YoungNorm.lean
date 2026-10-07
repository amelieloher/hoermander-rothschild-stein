-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.YoungFinite
public import RothschildStein.G2.ConvolutionMeasurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

/-- The finite-output Young bound for real or complex Bochner
convolution, with constant one (BB Prop 3.45, p. 119). -/
theorem eLpNorm_groupConvolution_le_finite {f g : (Fin N → ℝ) → 𝕜}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (he : 1 / p + 1 / q = 1 + 1 / r) :
    eLpNorm (groupConvolution G f g) (ENNReal.ofReal r) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume * eLpNorm g (ENNReal.ofReal q) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpow : (∫⁻ x, ‖groupConvolution G f g x‖ₑ ^ r) ≤
      (∫⁻ x, ‖f x‖ₑ ^ p) ^ (r / p) * (∫⁻ x, ‖g x‖ₑ ^ q) ^ (r / q) :=
    (lintegral_mono fun x => ENNReal.rpow_le_rpow
      (enorm_groupConvolution_le G f g x) hr0.le).trans
      (young_groupConvolution_power G hf.measurable.enorm hg.measurable.enorm hp hq hr he)
  have H := ENNReal.rpow_le_rpow hpow (div_nonneg zero_le_one hr0.le)
  have hrp : (r / p) * (1 / r) = 1 / p := by field_simp
  have hrq : (r / q) * (1 / r) = 1 / q := by field_simp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr0).ne'
    ENNReal.ofReal_ne_top (stronglyMeasurable_groupConvolution G hf hg).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq0).ne'
    ENNReal.ofReal_ne_top hg.aestronglyMeasurable]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hr0.le),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hrp, hrq] at H
  simpa only [ENNReal.toReal_ofReal hr0.le, ENNReal.toReal_ofReal hp0.le,
    ENNReal.toReal_ofReal hq0.le] using H

end RothschildStein.G2
