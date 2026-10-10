-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionLaterEstimates
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Open-top essential bounds with finite reciprocal source norms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Uniform terminal estimates expressed through a finite real source norm
extend to the open top time. Finiteness of the full source norm makes its real
value monotone under restriction. The result applies directly to reciprocal
iteration estimates, without an essential bound on the original solution. -/
theorem eLpNormEssSup_prod_Ioo_le_of_ae_terminal_real_norm_bounds
    {E : Type*} [MeasurableSpace E] (μ : Measure (ℝ × E))
    {a a' c T : ℝ} (hcT : c < T) (B B' : Set E)
    (f : ℝ × E → ℝ) (p : ℝ≥0∞) {C : ℝ} (hC : 0 ≤ C)
    (hfinite : eLpNorm f p (μ.restrict (Icc a T ×ˢ B)) < ⊤)
    (hbound : ∀ᵐ s ∂volume.restrict (Ioo c T),
      eLpNormEssSup f (μ.restrict (Ioo a' s ×ˢ B')) ≤
        ENNReal.ofReal (C * (eLpNorm f p (μ.restrict (Icc a s ×ˢ B))).toReal)) :
    eLpNormEssSup f (μ.restrict (Ioo a' T ×ˢ B')) ≤
      ENNReal.ofReal (C * (eLpNorm f p (μ.restrict (Icc a T ×ˢ B))).toReal) := by
  change essSup (fun z => ‖f z‖ₑ) (μ.restrict (Ioo a' T ×ˢ B')) ≤ _
  apply essSup_prod_Ioo_le_of_ae_cofinal_terminal_bounds μ hcT B' (fun z => ‖f z‖ₑ)
  filter_upwards [hbound, self_mem_ae_restrict measurableSet_Ioo] with s hs hst
  apply hs.trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hC
  apply ENNReal.toReal_mono hfinite.ne
  apply eLpNorm_mono_measure
  apply Measure.restrict_mono _ le_rfl
  exact Set.prod_mono (Icc_subset_Icc_right hst.2.le) Subset.rfl

end HeatKernel
