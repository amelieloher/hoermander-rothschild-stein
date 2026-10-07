-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.S
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The finite-measure Jensen/Hölder inequality in extended
nonnegative form, including exponent one, zero mass, and infinite
integrals (BB Lemma 2.11, p. 74; endpoint). -/
theorem lintegral_rpow_le_mass_rpow_mul {F : α → ℝ≥0∞}
    (hF : AEMeasurable F μ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, F x ∂μ)^p ≤ (μ Set.univ)^(p-1) * ∫⁻ x, (F x)^p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ha : 0 ≤ p⁻¹ := (inv_pos.mpr hp0).le
  have hb : 0 ≤ 1-p⁻¹ := sub_nonneg.mpr ((inv_le_one₀ hp0).mpr hp)
  have H := ENNReal.lintegral_mul_norm_pow_le (hF.pow_const p)
    (aemeasurable_const (b := (1 : ℝ≥0∞))) ha hb (by ring : p⁻¹+(1-p⁻¹)=1)
  have hpp : p*p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have he : (1-p⁻¹)*p = p-1 := by rw [sub_mul,one_mul,inv_mul_cancel₀ hp0.ne']
  simp only [← ENNReal.rpow_mul,hpp,ENNReal.rpow_one,ENNReal.one_rpow,mul_one,
    lintegral_one] at H
  have H' := ENNReal.rpow_le_rpow H hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,← ENNReal.rpow_mul,
    inv_mul_cancel₀ hp0.ne',ENNReal.rpow_one,← ENNReal.rpow_mul,he,mul_comm] at H'
  exact H'

end RothschildStein.S
