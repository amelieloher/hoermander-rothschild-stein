-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FiniteMeasureJensen
public import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace RothschildStein.S
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- Jensen followed by Tonelli bounds a kernel envelope's
integrated p-th power by the uniform translated p-moment. The argument
includes p=1 (BB Lemma 2.11, p. 74; endpoint). -/
theorem lintegral_kernelEnvelope_rpow_le
    {F : α → β → ℝ≥0∞} (hF : Measurable (uncurry F))
    {Q : α → ℝ≥0∞} {C M : ℝ≥0∞}
    {p : ℝ} (hp : 1 ≤ p)
    (hQ : ∀ᵐ x ∂μ, Q x ≤ C * ∫⁻ y, F x y ∂ν)
    (hM : ∀ᵐ y ∂ν, (∫⁻ x, (F x y)^p ∂μ) ≤ M) :
    (∫⁻ x, (Q x)^p ∂μ) ≤ C^p * (ν univ)^(p-1) * (ν univ * M) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hm : Measurable (fun x => ∫⁻ y, (F x y)^p ∂ν) :=
    (hF.pow_const p).lintegral_prod_right
  calc
    (∫⁻ x, (Q x)^p ∂μ) ≤
        ∫⁻ x, C^p * ((ν univ)^(p-1) * ∫⁻ y, (F x y)^p ∂ν) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hQ] with x hx
      have H := ENNReal.rpow_le_rpow hx hp0.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at H
      exact H.trans (mul_le_mul_right (lintegral_rpow_le_mass_rpow_mul
        hF.of_uncurry_left.aemeasurable hp) (C^p))
    _ = C^p * (ν univ)^(p-1) * ∫⁻ x, ∫⁻ y, (F x y)^p ∂ν ∂μ := by
      simp_rw [← mul_assoc]
      rw [lintegral_const_mul'' _ hm.aemeasurable]
    _ = C^p * (ν univ)^(p-1) * ∫⁻ y, ∫⁻ x, (F x y)^p ∂μ ∂ν := by
      rw [lintegral_lintegral_swap (hF.pow_const p).aemeasurable]
    _ ≤ C^p * (ν univ)^(p-1) * (ν univ * M) := by
      apply mul_le_mul_right
      have H := lintegral_mono_ae hM
      simpa only [lintegral_const,mul_comm] using H

end RothschildStein.S
