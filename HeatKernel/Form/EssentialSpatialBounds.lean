-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ProductL2
public import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Tactic.Linter

/-! # Product L² bounds from essential spatial L² bounds -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace HeatKernel

/-- On a finite parameter measure, a jointly measurable function with essentially bounded
spatial L² seminorm is square integrable on the product measure. -/
theorem memLp_product_of_essSup_spatial_eLpNorm_lt_top {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν] {f : α → β → E}
    (hf : AEStronglyMeasurable (Function.uncurry f) (μ.prod ν))
    (hb : essSup (fun t => eLpNorm (f t) 2 ν) μ < ⊤) :
    MemLp (Function.uncurry f) 2 (μ.prod ν) := by
  rw [memLp_iff]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_prod _ (hf.enorm.pow_const (2 : ℝ))]
  have hpoint : ∀ᵐ t ∂μ, (∫⁻ x, ‖f t x‖ₑ ^ (2 : ℝ) ∂ν) ≤
      (essSup (fun t => eLpNorm (f t) 2 ν) μ) ^ (2 : ℕ) := by
    filter_upwards [hf.prodMk_left, ENNReal.ae_le_essSup (fun t => eLpNorm (f t) 2 ν)] with t ht hbt
    have ht' : AEStronglyMeasurable (f t) ν := by simpa only [Function.uncurry_def] using ht
    have he : (eLpNorm (f t) 2 ν) ^ (2 : ℕ) = ∫⁻ x, ‖f t x‖ₑ ^ (2 : ℝ) ∂ν := by
      simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) ht'
    rw [← he]
    exact pow_le_pow_left₀ bot_le hbt 2
  exact (lintegral_mono_ae hpoint).trans_lt (by
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hb) (measure_lt_top μ univ))



end HeatKernel
