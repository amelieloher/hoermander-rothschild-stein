-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.WithDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- Weighted Hölder with the absolute row kernel as density.
This is the first inequality in the proof of Schur's bound; no
integrability or nonzero row-mass premise is required. -/
theorem weightedKernel_holder_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K : α → ℝ≥0∞) (hK : AEMeasurable K μ)
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ y, K y * ‖f y‖ₑ ∂μ) ≤
      (∫⁻ y, K y * ‖f y‖ₑ ^ p ∂μ) ^ (1 / p) *
        (∫⁻ y, K y ∂μ) ^ (1 - 1 / p) := by
  have hfw : AEStronglyMeasurable f (μ.withDensity K) :=
    hf.mono_ac (withDensity_absolutelyContinuous μ K)
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (by norm_num : (0 : ℝ) < 1) hp hfw
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm] at h
  simp only [ENNReal.rpow_one, one_div_one] at h
  rw [lintegral_withDensity_eq_lintegral_mul₀ hK hf.enorm,
    lintegral_withDensity_eq_lintegral_mul₀ hK (hf.enorm.pow_const p),
    withDensity_apply K MeasurableSet.univ, Measure.restrict_univ] at h
  simpa using h

end RothschildStein.P1
