-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueScaledMeasures
import Mathlib.Tactic

/-! # Exact parabolic scaling of integral and supremum norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Every finite positive power norm acquires the corresponding root of the
pushforward Jacobian on inverse-image domains. -/
theorem eLpNorm_comp_restrict_of_scaled_measure
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₜ E) (μ : Measure E) {J : ℝ≥0∞}
    (hm : Measure.map T μ = J • μ) (f : E → ℝ) (S : Set E)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm (f ∘ T) (ENNReal.ofReal p) (μ.restrict (T ⁻¹' S)) =
      J ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) (μ.restrict S) := by
  rw [← T.measurableEmbedding.eLpNorm_map_measure,
    map_restrict_preimage_of_scaled_measure T μ hm S,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top]
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, smul_eq_mul]

/-- A nonzero Jacobian leaves the essential supremum unchanged. -/
theorem eLpNormEssSup_comp_restrict_of_scaled_measure
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : E ≃ₜ E) (μ : Measure E) {J : ℝ≥0∞}
    (hm : Measure.map T μ = J • μ) (hJ : J ≠ 0) (f : E → ℝ) (S : Set E) :
    eLpNormEssSup (f ∘ T) (μ.restrict (T ⁻¹' S)) =
      eLpNormEssSup f (μ.restrict S) := by
  rw [← T.measurableEmbedding.eLpNormEssSup_map_measure,
    map_restrict_preimage_of_scaled_measure T μ hm S,
    eLpNormEssSup_ennreal_smul_measure hJ]

end HeatKernel
