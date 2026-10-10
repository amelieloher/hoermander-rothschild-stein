-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # Essential bounds from positive and negative parts -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Taking the positive part contracts the absolute value. -/
theorem norm_positivePart_le (s : ℝ) : ‖max s 0‖ ≤ ‖s‖ := by
  by_cases hs : 0 ≤ s
  · rw [max_eq_left hs]
  · rw [max_eq_right (lt_of_not_ge hs).le, norm_zero]
    exact norm_nonneg _

/-- A common essential bound for the positive and negative parts bounds the signed function. -/
theorem eLpNormEssSup_le_of_positive_negative_parts {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {K : ℝ≥0∞}
    (hp : eLpNormEssSup (fun x => max (f x) 0) μ ≤ K)
    (hn : eLpNormEssSup (fun x => max (-f x) 0) μ ≤ K) :
    eLpNormEssSup f μ ≤ K := by
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [enorm_ae_le_eLpNormEssSup (fun x => max (f x) 0) μ,
    enorm_ae_le_eLpNormEssSup (fun x => max (-f x) 0) μ] with x hx hy
  by_cases hs : 0 ≤ f x
  · simpa only [max_eq_left hs] using hx.trans hp
  · have hsn : 0 ≤ -f x := neg_nonneg.mpr (lt_of_not_ge hs).le
    simpa only [max_eq_left hsn, enorm_neg] using hy.trans hn

/-- Mean-value bounds for both parts give the same bound for the signed function. -/
theorem eLpNormEssSup_le_mul_eLpNorm_of_positive_negative_parts
    {α : Type*} [MeasurableSpace α] {μinner μouter : Measure α}
    {f : α → ℝ} {p C : ℝ≥0∞} (hf : AEStronglyMeasurable f μouter)
    (hp : eLpNormEssSup (fun x => max (f x) 0) μinner ≤
      C * eLpNorm (fun x => max (f x) 0) p μouter)
    (hn : eLpNormEssSup (fun x => max (-f x) 0) μinner ≤
      C * eLpNorm (fun x => max (-f x) 0) p μouter) :
    eLpNormEssSup f μinner ≤ C * eLpNorm f p μouter := by
  apply eLpNormEssSup_le_of_positive_negative_parts
  · exact hp.trans (mul_le_mul' le_rfl (eLpNorm_mono_ae
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable hf)
      (Filter.Eventually.of_forall fun x => norm_positivePart_le (f x))))
  · exact hn.trans (mul_le_mul' le_rfl (eLpNorm_mono_ae
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable hf.neg)
      (Filter.Eventually.of_forall fun x => by
        simpa only [norm_neg] using norm_positivePart_le (-f x))))

end HeatKernel
