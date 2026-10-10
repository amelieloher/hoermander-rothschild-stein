-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SquareIntegrableSlices
import Mathlib.Tactic

/-! # From a uniform spatial square-integrability bound to product square integrability -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace HeatKernel

/-- A measurable function with essentially bounded spatial L² norm is square
integrable on a product with a finite time measure. -/
theorem memLp_two_prod_of_ae_slice_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {f : α × β → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν))
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ᵐ t ∂μ, eLpNorm (fun x => f (t, x)) 2 ν ≤ C) : MemLp f 2 (μ.prod ν) := by
  have hquad : (∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ.prod ν) ≤ C ^ 2 * μ univ := by
    rw [lintegral_prod _ (hf.enorm.pow_const (2 : ℕ))]
    calc
      _ ≤ ∫⁻ _t, C ^ 2 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hf.prodMk_left, hbound] with t hmt ht
        have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hmt
        norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at he
        rw [← he]
        exact pow_le_pow_left' ht 2
      _ = C ^ 2 * μ univ := lintegral_const _
  have hfin : (∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ.prod ν) < ⊤ :=
    hquad.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top hC) (measure_lt_top μ univ))
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hf).mpr
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hfin

/-- A finite essential supremum of the spatial L² norms suffices for product L² membership. -/
theorem memLp_two_prod_of_essSup_slice_lt_top {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]
    {f : α × β → ℝ} (hf : AEStronglyMeasurable f (μ.prod ν))
    (hbound : essSup (fun t => eLpNorm (fun x => f (t, x)) 2 ν) μ < ⊤) :
    MemLp f 2 (μ.prod ν) :=
  memLp_two_prod_of_ae_slice_bound hf hbound (ENNReal.ae_le_essSup _)

end HeatKernel
