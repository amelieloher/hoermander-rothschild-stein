-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # Higher-power consequences of quadratic mean-value estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- A quadratic mean-value estimate implies every higher-power estimate, with the
explicit outer-volume normalization. -/
theorem eLpNormEssSup_le_higher_power_of_quadratic_bound
    {α : Type*} [MeasurableSpace α] (μinner μouter : Measure α) {f : α → ℝ}
    {C : ℝ≥0∞} {p : ℝ} (hp : 2 ≤ p) (hf : AEStronglyMeasurable f μouter)
    (hmean : eLpNormEssSup f μinner ≤ C * eLpNorm f 2 μouter) :
    eLpNormEssSup f μinner ≤ C *
      (eLpNorm f (ENNReal.ofReal p) μouter * μouter Set.univ ^ (1 / 2 - 1 / p)) := by
  apply hmean.trans
  apply mul_le_mul' le_rfl
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (2 : ℝ≥0∞) ≤ ENNReal.ofReal p by
      simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp) hf
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using h

/-- On any fixed finite outer measure, a quadratic mean-value constant gives a
finite positive constant for each larger exponent, uniformly in the inner
measure and function. -/
theorem exists_higher_power_constant_of_quadratic_bound
    {α : Type*} [MeasurableSpace α] (μouter : Measure α)
    (hμouter : μouter Set.univ ≠ ⊤) {p A : ℝ} (hp : 2 ≤ p) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μinner : Measure α) (f : α → ℝ),
      AEStronglyMeasurable f μouter →
      eLpNormEssSup f μinner ≤ ENNReal.ofReal A * eLpNorm f 2 μouter →
      eLpNormEssSup f μinner ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μouter := by
  let e := 1 / 2 - 1 / p
  let b := (μouter Set.univ).toReal
  let C := A * (b ^ e + 1)
  have he : 0 ≤ e := sub_nonneg.mpr
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp)
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hC : 0 < C := mul_pos hA (by linarith [Real.rpow_nonneg hb e])
  refine ⟨C, hC, ?_⟩
  intro μinner f hf hmean
  have h := eLpNormEssSup_le_higher_power_of_quadratic_bound μinner μouter hp hf hmean
  have hfactor : μouter Set.univ ^ e ≤ ENNReal.ofReal (b ^ e + 1) := by
    have heq : μouter Set.univ ^ e = ENNReal.ofReal (b ^ e) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hb he, ENNReal.ofReal_toReal hμouter]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ ENNReal.ofReal A *
        (eLpNorm f (ENNReal.ofReal p) μouter * μouter Set.univ ^ e) := h
    _ ≤ ENNReal.ofReal A *
        (eLpNorm f (ENNReal.ofReal p) μouter * ENNReal.ofReal (b ^ e + 1)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hfactor)
    _ = _ := by
      dsimp only [C]
      rw [ENNReal.ofReal_mul hA.le]
      ac_rfl

end HeatKernel
