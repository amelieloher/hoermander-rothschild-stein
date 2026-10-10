-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiNestingIteration
public import Mathlib.MeasureTheory.Function.EssSup

/-! # Logarithmic coordinates for finite nonnegative essential suprema -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- The nonnegative logarithmic coordinate of a finite nonnegative quantity. -/
def nonnegativeLogSupremum (s : ℝ≥0∞) : ℝ := max 0 (Real.log s.toReal)

/-- A finite nonnegative quantity is bounded by its logarithmic exponential cap. -/
theorem le_exp_nonnegativeLogSupremum {s : ℝ≥0∞} (hs : s ≠ ⊤) :
    s ≤ ENNReal.ofReal (Real.exp (nonnegativeLogSupremum s)) := by
  have he : s.toReal ≤ Real.exp (nonnegativeLogSupremum s) := by
    by_cases hz : s = 0
    · simp only [hz, ENNReal.toReal_zero]
      exact (Real.exp_pos _).le
    · have hp := ENNReal.toReal_pos hz hs
      calc
        s.toReal = Real.exp (Real.log s.toReal) := (Real.exp_log hp).symm
        _ ≤ Real.exp (max 0 (Real.log s.toReal)) :=
          Real.exp_le_exp.mpr (le_max_right _ _)
  calc
    s = ENNReal.ofReal s.toReal := (ENNReal.ofReal_toReal hs).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal he

/-- The logarithmic coordinate is monotone below a finite upper quantity. -/
theorem nonnegativeLogSupremum_mono {s t : ℝ≥0∞} (ht : t ≠ ⊤) (hst : s ≤ t) :
    nonnegativeLogSupremum s ≤ nonnegativeLogSupremum t := by
  by_cases hz : s = 0
  · simp only [hz, nonnegativeLogSupremum, ENNReal.toReal_zero, Real.log_zero, max_self]
    exact le_max_left _ _
  · have hs : s ≠ ⊤ := ne_top_of_le_ne_top ht hst
    apply max_le_max_left
    exact Real.log_le_log (ENNReal.toReal_pos hz hs) (ENNReal.toReal_mono ht hst)

/-- A moment mean-value bound gives its precise logarithmic form, including the
case when the moment vanishes. -/
theorem nonnegativeLogSupremum_le_of_meanValue {s m : ℝ≥0∞} {p C : ℝ}
    (hp : 0 < p) (hm : m ≠ ⊤)
    (hmean : s ≤ (ENNReal.ofReal (Real.exp C) * m) ^ (1 / p)) :
    nonnegativeLogSupremum s ≤ max 0 ((C + Real.log m.toReal) / p) := by
  by_cases hs : s = 0
  · simp only [hs, nonnegativeLogSupremum, ENNReal.toReal_zero, Real.log_zero, max_self]
    exact le_max_left _ _
  have hm0 : m ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)] at hmean
    exact hs (le_zero_iff.mp hmean)
  have hb : ENNReal.ofReal (Real.exp C) * m ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm
  have hr : (ENNReal.ofReal (Real.exp C) * m) ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp.le) hb
  have hsfin := ne_top_of_le_ne_top hr hmean
  have ht := ENNReal.toReal_mono hr hmean
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos C).le] at ht
  have hl := Real.log_le_log (ENNReal.toReal_pos hs hsfin) ht
  rw [Real.log_rpow (mul_pos (Real.exp_pos C) (ENNReal.toReal_pos hm0 hm)),
    Real.log_mul (Real.exp_ne_zero _) (ENNReal.toReal_pos hm0 hm).ne', Real.log_exp] at hl
  apply max_le_max_left
  convert hl using 1
  ring

/-- Finite outer essential supremum and normalized finite measure make every
positive moment finite. -/
theorem lintegral_rpow_ne_top_of_essSup_ne_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℝ≥0∞) {U V : Set α} (hUV : U ⊆ V)
    (hμV : μ V ≤ 1) (hfinite : essSup f (μ.restrict V) ≠ ⊤)
    {p : ℝ} (hp : 0 ≤ p) : (∫⁻ y in U, f y ^ p ∂μ) ≠ ⊤ := by
  have hcap : ∀ᵐ y ∂μ.restrict U, f y ≤ essSup f (μ.restrict V) :=
    ae_restrict_of_ae_restrict_of_subset hUV (ENNReal.ae_le_essSup f)
  have hμU : μ U ≤ 1 := (measure_mono hUV).trans hμV
  have hbound : (∫⁻ y in U, f y ^ p ∂μ) ≤ essSup f (μ.restrict V) ^ p := by
    calc
      _ ≤ ∫⁻ _y in U, essSup f (μ.restrict V) ^ p ∂μ :=
        lintegral_mono_ae (hcap.mono fun _ hy => ENNReal.rpow_le_rpow hy hp)
      _ = essSup f (μ.restrict V) ^ p * μ U := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_right hμU (essSup f (μ.restrict V) ^ p)
  exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hp hfinite) hbound

end HeatKernel
