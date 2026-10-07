-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SchurIntegralExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- Changing an input on a null set leaves every output
integral unchanged, so the operator descends to Lp equivalence classes. -/
theorem integralOperator_eq_of_ae_eq {α β : Type*}
    [MeasurableSpace β] (ν : Measure β) (K : α → β → ℝ)
    {f g : β → ℝ} (hfg : f =ᵐ[ν] g) :
    (fun x => ∫ y, K x y * f y ∂ν) = (fun x => ∫ y, K x y * g y ∂ν) := by
  funext x
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- Every Lp input has an actual Lp output and an absolutely
convergent kernel integral at almost every output point. The statement
requires no extra measurability hypothesis on the chosen Lp representative. -/
theorem integralOperator_memLp_and_integrable_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (K : α → β → ℝ)
    (hK : Measurable (Function.uncurry K)) (A B : ℝ≥0∞) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hrow : ∀ x, (∫⁻ y, ‖K x y‖ₑ ∂ν) ≤ A)
    (hcolumn : ∀ y, (∫⁻ x, ‖K x y‖ₑ ∂μ) ≤ B)
    (f : β → ℝ) {p : ℝ} (hp : 1 ≤ p) (hfp : MemLp f (ENNReal.ofReal p) ν) :
    MemLp (fun x => ∫ y, K x y * f y ∂ν) (ENNReal.ofReal p) μ ∧
      ∀ᵐ x ∂μ, Integrable (fun y => K x y * f y) ν := by
  let hm := hfp.aemeasurable
  let g := hm.mk f
  have hg : Measurable g := hm.measurable_mk
  have he : f =ᵐ[ν] g := hm.ae_eq_mk
  have hgp : MemLp g (ENNReal.ofReal p) ν := hfp.ae_eq he
  have hmg := integralOperator_memLp μ ν K hK A B hA hB hrow hcolumn g hg hp hgp
  have hig := integralOperator_integrable_ae μ ν K hK A B hA hB hrow hcolumn g hg hp hgp
  constructor
  · rw [integralOperator_eq_of_ae_eq ν K he]
    exact hmg
  · filter_upwards [hig] with x hx
    apply hx.congr
    filter_upwards [he] with y hy
    rw [hy]

end RothschildStein.P1
