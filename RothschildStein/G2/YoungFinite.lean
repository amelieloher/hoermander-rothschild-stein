-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.YoungPower

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Young's inequality in power-integral form for finite output
exponents. Infinite input integrals are allowed, and the constant is one
(BB Prop 3.45, p. 119). -/
theorem young_groupConvolution_power {f g : (Fin N → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (he : 1 / p + 1 / q = 1 + 1 / r) :
    (∫⁻ x, lgroupConvolution G f g x ^ r) ≤
      (∫⁻ x, f x ^ p) ^ (r / p) * (∫⁻ x, g x ^ q) ^ (r / q) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpinv : 1 / p ≤ 1 := (div_le_one hp0).mpr hp
  have hqinv : 1 / q ≤ 1 := (div_le_one hq0).mpr hq
  have hb : 0 ≤ 1 / p - 1 / r := by linarith
  have hc : 0 ≤ 1 / q - 1 / r := by linarith
  have hs : 1 / r + (1 / p - 1 / r) + (1 / q - 1 / r) = 1 := by linarith
  have hpw : p * (1 / r + (1 / p - 1 / r)) = 1 := by
    rw [add_sub_cancel]
    exact mul_one_div_cancel hp0.ne'
  have hqw : q * (1 / r + (1 / q - 1 / r)) = 1 := by
    rw [add_sub_cancel]
    exact mul_one_div_cancel hq0.ne'
  have har : 1 / r * r = 1 := one_div_mul_cancel hr0.ne'
  have H := lintegral_lgroupConvolution_rpow_le G hf hg hr0
    (div_nonneg zero_le_one hr0.le) hb hc hs hpw hqw har
  have hbr : 1 + (1 / p - 1 / r) * r = r / p := by
    field_simp
    ring
  have hcr : 1 + (1 / q - 1 / r) * r = r / q := by
    field_simp
    ring
  have hab (A B : ℝ≥0∞) :
      (A * B) * A ^ ((1 / p - 1 / r) * r) * B ^ ((1 / q - 1 / r) * r) =
        A ^ (r / p) * B ^ (r / q) := by
    calc
      _ = (A ^ (1 : ℝ) * A ^ ((1 / p - 1 / r) * r)) *
          (B ^ (1 : ℝ) * B ^ ((1 / q - 1 / r) * r)) := by
        simp only [ENNReal.rpow_one]
        ac_rfl
      _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (mul_nonneg hb hr0.le),
          ← ENNReal.rpow_add_of_nonneg _ _ zero_le_one (mul_nonneg hc hr0.le), hbr, hcr]
  simpa only [hab] using H

end RothschildStein.G2
