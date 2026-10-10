-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Product almost everywhere equality from measurable slice representatives -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- Slice almost everywhere equality of jointly almost everywhere measurable real
functions implies equality for the product measure. -/
theorem ae_eq_of_jointly_aemeasurable_of_ae_slice_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] {f g : α × β → ℝ}
    (hf : AEMeasurable f (μ.prod ν)) (hg : AEMeasurable g (μ.prod ν))
    (he : ∀ᵐ t ∂μ, (fun x => f (t, x)) =ᵐ[ν] fun x => g (t, x)) :
    f =ᵐ[μ.prod ν] g := by
  have hm : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk)).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hg.ae_eq_mk, he] with t hft hgt het
    filter_upwards [hft, hgt, het] with x hfx hgx hex
    exact hfx.symm.trans (hex.trans hgx)
  exact hf.ae_eq_mk.trans (hm.trans hg.ae_eq_mk.symm)

end HeatKernel
