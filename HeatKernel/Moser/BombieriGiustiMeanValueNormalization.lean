-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiRelativeReverseHolder
import Mathlib.Tactic

/-! # Transfer of a mean-value estimate to an outer reference measure

A source cylinder contained in the moment cylinder can use the outer reference
measure at the cost of the fixed measure ratio raised to the reciprocal exponent.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Enlarging a moment domain and changing its reference measure costs the
reference-measure ratio to the reciprocal moment exponent. No moment finiteness
or measurability assumption is needed for this order comparison. -/
theorem normalized_moment_norm_le_of_measure_comparison
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {P V U : Set α} {R : ℝ≥0∞} {p : ℝ}
    (hp : 0 < p) (hPzero : μ P ≠ 0) (hUfinite : μ U ≠ ⊤)
    (hPV : P ⊆ V) (hPU : P ⊆ U) (hratio : μ U ≤ R * μ P) :
    ((μ P)⁻¹ * (∫⁻ y in P, f y ^ p ∂μ)) ^ (1 / p) ≤
      R ^ (1 / p) * ((μ U)⁻¹ * (∫⁻ y in V, f y ^ p ∂μ)) ^ (1 / p) := by
  have hPfinite : μ P ≠ ⊤ := ne_top_of_le_ne_top hUfinite (measure_mono hPU)
  have hUzero : μ U ≠ 0 := by
    intro hz
    exact hPzero (le_antisymm (hz ▸ measure_mono hPU) bot_le)
  have hdiv : μ U / μ P ≤ R :=
    (ENNReal.div_le_iff hPzero hPfinite).mpr (by simpa only [mul_comm] using hratio)
  have hinv : (μ P)⁻¹ ≤ R * (μ U)⁻¹ := by
    calc
      (μ P)⁻¹ = (μ U)⁻¹ * (μ U / μ P) := by
        rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel hUzero hUfinite, one_mul]
      _ ≤ (μ U)⁻¹ * R := mul_le_mul' le_rfl hdiv
      _ = R * (μ U)⁻¹ := mul_comm _ _
  have he := ENNReal.rpow_le_rpow
    (mul_le_mul' hinv (lintegral_mono_set (μ := μ) (f := fun y => f y ^ p) hPV))
    (one_div_nonneg.mpr hp.le)
  calc
    _ ≤ (R * ((μ U)⁻¹ * (∫⁻ y in V, f y ^ p ∂μ))) ^ (1 / p) := by
      simpa only [mul_assoc] using he
    _ = _ := ENNReal.mul_rpow_of_nonneg R _ (one_div_nonneg.mpr hp.le)

/-- A fixed-exponent mean-value estimate on a source set transfers to the
larger moment set with the exact fixed reference-measure cost. -/
theorem essSup_le_normalized_moment_of_measure_comparison
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} {S P V U : Set α} {K R p : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hPzero : μ P ≠ 0) (hUfinite : μ U ≠ ⊤)
    (hPV : P ⊆ V) (hPU : P ⊆ U) (hratio : μ U ≤ ENNReal.ofReal R * μ P)
    (hmean : essSup f (μ.restrict S) ≤ ENNReal.ofReal K *
      ((μ P)⁻¹ * (∫⁻ y in P, f y ^ p ∂μ)) ^ (1 / p)) :
    essSup f (μ.restrict S) ≤ ENNReal.ofReal (K * R ^ (1 / p)) *
      ((μ U)⁻¹ * (∫⁻ y in V, f y ^ p ∂μ)) ^ (1 / p) := by
  have he := normalized_moment_norm_le_of_measure_comparison
    hp hPzero hUfinite hPV hPU hratio (f := f)
  calc
    _ ≤ ENNReal.ofReal K * ((μ P)⁻¹ * (∫⁻ y in P, f y ^ p ∂μ)) ^ (1 / p) := hmean
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal R ^ (1 / p) *
        ((μ U)⁻¹ * (∫⁻ y in V, f y ^ p ∂μ)) ^ (1 / p)) := mul_le_mul' le_rfl he
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hR (one_div_nonneg.mpr hp.le),
        ← mul_assoc, ← ENNReal.ofReal_mul hK]

end HeatKernel
