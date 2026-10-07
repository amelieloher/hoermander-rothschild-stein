-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZBounds
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

theorem czAverage_le_laverage_bound (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hpos : ∀ i, μ (B i) ≠ 0) (hfinite : ∀ x, {i | x ∈ B i}.Finite)
    (f : X → ℝ) (hf : Integrable f μ) {L : ℝ} (hL : 0 ≤ L) (i : ι)
    (havg : (⨍⁻ x in B i, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal L) :
    czAverage μ B f i ≤ L := by
  have hden : 0 < (μ (B i)).toReal := ENNReal.toReal_pos (hpos i) (hμ i)
  have hi := (hf.norm.indicator (hB i))
  have hnum : (∫ x, czWeighted B f i x ∂μ) ≤ ∫ x in B i, ‖f x‖ ∂μ := by
    rw [← integral_indicator (hB i)]
    apply integral_mono_ae (czWeighted_integrable μ B hB hfinite f hf i) hi
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ B i
      · rw [indicator_of_mem hx]
        calc
          _ ≤ ‖f x * coverWeight B i x‖ := le_abs_self _
          _ ≤ ‖f x‖ := by
            rw [norm_mul, Real.norm_of_nonneg (coverWeight_nonneg_le_one B x (hfinite x) i).1]
            exact mul_le_of_le_one_right (norm_nonneg _) (coverWeight_nonneg_le_one B x (hfinite x) i).2
      · simp [czWeighted, coverWeight, hx]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top havg
  rw [setLAverage_eq, ENNReal.toReal_div, ENNReal.toReal_ofReal hL,
    ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable.restrict] at ht
  exact (div_le_div_of_nonneg_right hnum hden.le).trans ht

end RothschildStein.H2
