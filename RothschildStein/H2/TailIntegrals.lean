-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Truncation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2

/-- The elementary lower-end power integral in the interpolation proof
(BB Thm 7.48, p. 334). -/
theorem lintegral_power_Ioo {r a : ℝ} (hr : -1 < r) (ha : 0 ≤ a) :
    ∫⁻ t in Ioo (0 : ℝ) a, ENNReal.ofReal (t ^ r) =
      ENNReal.ofReal (a ^ (r + 1) / (r + 1)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ r) (Ioo 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha,
      integral_rpow (Or.inl hr)]
    simp [Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _

/-- The elementary upper-end power integral in the interpolation proof
(BB Thm 7.48, p. 334). -/
theorem lintegral_power_Ioi {r a : ℝ} (hr : r < -1) (ha : 0 < a) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (t ^ r) =
      ENNReal.ofReal (a ^ (r + 1) / (-(r + 1))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr ha)]
  · rw [integral_Ioi_rpow_of_lt hr ha]
    congr 1; rw [neg_div, div_neg]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.trans ht).le _

variable {Y : Type*} [MeasurableSpace Y]

/-- Tonelli and the lower-end power integral evaluate the large-value
part exactly (BB Thm 7.48, p. 334). -/
theorem highPart_tail_integral (ν : Measure Y) [SFinite ν] {f : Y → ℝ}
    (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2)) * moment ν 1 (highPart f t) =
      ENNReal.ofReal (1 / (p - 1)) * moment ν p f := by
  have hmeas : Measurable (fun z : ℝ × Y =>
      if z.1 < |f z.2| then ENNReal.ofReal (z.1 ^ (p - 2)) * ENNReal.ofReal |f z.2|
      else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_fst (by simpa only [Real.norm_eq_abs, Function.comp_apply] using (hf.comp measurable_snd).norm))
    · fun_prop
    · fun_prop
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y,
        if t < |f y| then ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal |f y| else 0 ∂ν := by
      apply lintegral_congr
      intro t
      rw [moment, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      try dsimp only
      by_cases h : t < |f y| <;> simp [highPart, h]
    _ = ∫⁻ y, ∫⁻ t in Ioi (0 : ℝ),
        if t < |f y| then ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal |f y| else 0 ∂volume ∂ν :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (1 / (p - 1)) * ENNReal.ofReal (|f y| ^ p) ∂ν := by
      apply lintegral_congr
      intro y
      try dsimp only
      have he : Ioi (0 : ℝ) ∩ Iio |f y| = Ioo 0 |f y| := rfl
      rw [show (fun t : ℝ => if t < |f y| then
        ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal |f y| else 0) =
        (Iio |f y|).indicator (fun t => ENNReal.ofReal (t ^ (p - 2)) *
          ENNReal.ofReal |f y|) from rfl,
        lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        inter_comm, he, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        lintegral_power_Ioo (by linarith) (abs_nonneg _)]
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by linarith)),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      by_cases hy : |f y| = 0
      · simp [hy, Real.zero_rpow (by linarith : p - 2 + 1 ≠ 0),
          Real.zero_rpow (by linarith : p ≠ 0)]
      · have hypos := lt_of_le_of_ne (abs_nonneg (f y)) (Ne.symm hy)
        have hm : |f y| ^ (p - 2 + 1) * |f y| = |f y| ^ p := by
          calc
            _ = |f y| ^ (p - 2 + 1) * |f y| ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = |f y| ^ ((p - 2 + 1) + 1) := (Real.rpow_add hypos _ _).symm
            _ = _ := by congr 1; ring
        rw [div_mul_eq_mul_div, hm]
        ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Tonelli and the upper-end power integral evaluate the small-value
part exactly (BB Thm 7.48, p. 334). -/
theorem lowPart_tail_integral (ν : Measure Y) [SFinite ν] {f : Y → ℝ}
    (hf : Measurable f) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1 - q)) * moment ν q (lowPart f t) =
      ENNReal.ofReal (1 / (q - p)) * moment ν p f := by
  have hq : 0 < q := hp.trans hpq
  have hmeas : Measurable (fun z : ℝ × Y =>
      if |f z.2| ≤ z.1 then ENNReal.ofReal (z.1 ^ (p - 1 - q)) *
        ENNReal.ofReal (|f z.2| ^ q) else 0) := by
    apply Measurable.ite (measurableSet_le
      (by simpa only [Real.norm_eq_abs, Function.comp_apply] using (hf.comp measurable_snd).norm) measurable_fst)
    · fun_prop
    · fun_prop
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y,
        if |f y| ≤ t then ENNReal.ofReal (t ^ (p - 1 - q)) *
          ENNReal.ofReal (|f y| ^ q) else 0 ∂ν := by
      apply lintegral_congr
      intro t
      rw [moment, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      try dsimp only
      by_cases h : |f y| ≤ t <;>
        simp [lowPart, h, Real.zero_rpow hq.ne']
    _ = ∫⁻ y, ∫⁻ t in Ioi (0 : ℝ),
        if |f y| ≤ t then ENNReal.ofReal (t ^ (p - 1 - q)) *
          ENNReal.ofReal (|f y| ^ q) else 0 ∂volume ∂ν :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (1 / (q - p)) * ENNReal.ofReal (|f y| ^ p) ∂ν := by
      apply lintegral_congr
      intro y
      try dsimp only
      by_cases hy : |f y| = 0
      · simp [hy, Real.zero_rpow hq.ne', Real.zero_rpow hp.ne']
      · have hypos := lt_of_le_of_ne (abs_nonneg (f y)) (Ne.symm hy)
        rw [show (fun t : ℝ => if |f y| ≤ t then
          ENNReal.ofReal (t ^ (p - 1 - q)) * ENNReal.ofReal (|f y| ^ q) else 0) =
          (Ici |f y|).indicator (fun t => ENNReal.ofReal (t ^ (p - 1 - q)) *
            ENNReal.ofReal (|f y| ^ q)) from rfl,
          lintegral_indicator measurableSet_Ici,
          Measure.restrict_restrict measurableSet_Ici,
          show Ici |f y| ∩ Ioi (0 : ℝ) = Ici |f y| from
            inter_eq_left.mpr (fun t ht => hypos.trans_le ht),
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ← restrict_Ioi_eq_restrict_Ici,
          lintegral_power_Ioi (by linarith) hypos]
        rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by linarith)),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show -(p - 1 - q + 1) = q - p by ring,
          div_mul_eq_mul_div, ← Real.rpow_add hypos]
        rw [show p - 1 - q + 1 + q = p by ring]
        ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end RothschildStein.H2
