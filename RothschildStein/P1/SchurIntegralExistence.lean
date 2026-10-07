-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurMemLp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- The Schur integral exists absolutely for almost every
output point for each measurable Lp input, rather than relying on the
zero value assigned by the totalized integral outside its domain. -/
theorem integralOperator_integrable_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p)
    (hfp : MemLp f (ENNReal.ofReal p) ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => K x y * f y) ν := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hpower : (∫⁻ y, ‖f y‖ₑ ^ p ∂ν) < ⊤ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hpne ENNReal.ofReal_ne_top hfp
  have htotal := kernel_column_lintegral_bound μ ν (fun x y => ‖K x y‖ₑ) hK.enorm
    B hcolumn (fun y => ‖f y‖ₑ ^ p) (hf.enorm.pow_const p)
  have hfinite : (∫⁻ x, ∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ^ p ∂ν ∂μ) ≠ ⊤ :=
    (lt_of_le_of_lt htotal (ENNReal.mul_lt_top hB.lt_top hpower)).ne
  have hae := ae_lt_top (show Measurable (fun x => ∫⁻ y, ‖K x y‖ₑ * ‖f y‖ₑ ^ p ∂ν) by
    fun_prop) hfinite
  filter_upwards [hae] with x hx
  refine ⟨(hK.of_uncurry_left.mul hf).aestronglyMeasurable, ?_⟩
  change (∫⁻ y, ‖K x y * f y‖ₑ ∂ν) < ⊤
  simp only [enorm_mul]
  apply lt_of_le_of_lt (weightedKernel_holder_bound ν (fun y => ‖K x y‖ₑ)
    hK.of_uncurry_left.enorm.aemeasurable f hf.aestronglyMeasurable hp)
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hx.ne
  · exact ENNReal.rpow_lt_top_of_nonneg
      (by have : 1 / p ≤ 1 := (div_le_one hp0).mpr hp; linarith)
      (ne_top_of_le_ne_top hA (hrow x))

end RothschildStein.P1
