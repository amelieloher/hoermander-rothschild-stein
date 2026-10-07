-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- The measurable actual integral operator preserves Lp under
finite row and column bounds. This supplies the measurable-function
realization of the Schur estimate, not merely a formal moment bound. -/
theorem integralOperator_memLp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p)
    (hfp : MemLp f (ENNReal.ofReal p) ν) :
    MemLp (fun x => ∫ y, K x y * f y ∂ν) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have ht : StronglyMeasurable (fun x => ∫ y, K x y * f y ∂ν) :=
    (hK.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right
  have hbound := integralOperator_schur_eLpNorm'_bound μ ν K hK A B hrow hcolumn f hf hp
  have he1 := eLpNorm_eq_eLpNorm' (μ := μ) hpne ENNReal.ofReal_ne_top ht.aestronglyMeasurable
  have he2 := eLpNorm_eq_eLpNorm' (μ := ν) hpne ENNReal.ofReal_ne_top hfp.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal hp0.le] at he1 he2
  change eLpNorm _ _ _ < ⊤
  rw [he1]
  apply lt_of_le_of_lt hbound
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by have : 1 / p ≤ 1 := (div_le_one hp0).mpr hp; linarith) hA
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hB
  · rw [← he2]
    exact hfp

end RothschildStein.P1
