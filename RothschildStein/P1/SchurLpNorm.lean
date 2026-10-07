-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurLpRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- The full Schur inequality for arbitrary Lp representatives,
with the precise row and column factors and with no chosen-input measurability
premise. BB Proposition 11.10, p. 544. -/
theorem integralOperator_schur_eLpNorm_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) {p : ℝ} (hp : 1 ≤ p) (hfp : MemLp f (ENNReal.ofReal p) ν) :
    eLpNorm (fun x => ∫ y, K x y * f y ∂ν) (ENNReal.ofReal p) μ ≤
      A ^ (1 - 1 / p) * B ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) ν := by
  let hm := hfp.aemeasurable
  let g := hm.mk f
  have hg : Measurable g := hm.measurable_mk
  have he : f =ᵐ[ν] g := hm.ae_eq_mk
  have hgp : MemLp g (ENNReal.ofReal p) ν := hfp.ae_eq he
  have ht := (integralOperator_memLp_and_integrable_ae μ ν K hK A B hA hB
    hrow hcolumn g hp hgp).1.aestronglyMeasurable
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  rw [integralOperator_eq_of_ae_eq ν K he, eLpNorm_congr_ae he,
    eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top ht,
    eLpNorm_eq_eLpNorm' hpne ENNReal.ofReal_ne_top hgp.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  exact integralOperator_schur_eLpNorm'_bound μ ν K hK A B hrow hcolumn g hg hp

end RothschildStein.P1
