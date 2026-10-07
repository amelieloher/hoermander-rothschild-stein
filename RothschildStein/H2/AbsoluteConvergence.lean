-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2

/-- Positivity of the explicit volume-integral constant. -/
theorem volumeIntegralConstant_pos {C α : ℝ} (hC : 0 < C) (hα : 0 < α) :
    0 < volumeIntegralConstant C α := by
  apply div_pos hC
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hα))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Absolute convergence and explicit L1 bound for the regularized
integral. BB Theorem 7.12(a), p. 302; the fractional exponent is retained. -/
theorem SupportedKernel.regularized_absolute {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    {δ : ℝ≥0} (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x : X} (hx : x ∈ E) :
    IntegrableOn (fun y => K x y * (f y - f x)) G D.μ ∧
      (∫⁻ y in G, ENNReal.ofReal |K x y * (f y - f x)| ∂D.μ) ≤
        ENNReal.ofReal (A * (holderSemi δ G f).toReal *
          volumeIntegralConstant D.C_D (ν + (δ : ℝ)) * R ^ (ν + (δ : ℝ))) := by
  have hxG := hK.sub_EG hx
  have hα : 0 < ν + (δ : ℝ) := add_pos_of_nonneg_of_pos hK.kernel.ν_nonneg hδ
  have hA : 0 ≤ A * (holderSemi δ G f).toReal := mul_nonneg hK.kernel.A_nonneg ENNReal.toReal_nonneg
  have hbound := D.outerPatch.lintegral_abs_le_inner (hK.sub_G hxG) hK.kernel.measurable_E
    hK.radius_pos (hK.radius_le.trans (by change 3 * D.κ ≤ 6 * D.κ; have := D.κ_pos; linarith)) hα hA
    (g := fun y => K x y * (f y - f x))
    (fun y hy hr => by rw [hK.support x hx y hy hr, zero_mul])
    (by
      filter_upwards [ae_restrict_mem hK.kernel.measurable_E] with y hy
      intro hxy
      have h₁ := hK.kernel.size x hxG y hy hxy
      have h₂ := sub_le_holderSemi hf.parts.2 hy hxG
      rw [dist_comm y x] at h₂
      rw [abs_mul]
      have he := mul_le_mul h₁ h₂ (abs_nonneg _) (mul_nonneg hK.kernel.A_nonneg (kernelWeight_nonneg _ _ _ _))
      refine he.trans_eq ?_
      change A * kernelWeight D.μ ν x y * _ = A * (holderSemi δ G f).toReal * kernelWeight D.μ (ν + (δ : ℝ)) x y
      unfold kernelWeight
      rw [Real.rpow_add (dist_pos.mpr hxy)]
      ring)
  refine ⟨integrableOn_of_subtype_lintegral hK.kernel.measurable_E ?_
    (hbound.trans_lt ENNReal.ofReal_lt_top), hbound⟩
  exact ((hK.kernel.measurable_slice hxG).mul
    ((hf.measurable_subtype hδ).sub measurable_const)).aestronglyMeasurable

/-- The regularized integral has the corresponding absolute bound. -/
theorem SupportedKernel.regularized_abs_le {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    {δ : ℝ≥0} (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x : X} (hx : x ∈ E) :
    |regularizedIntegral D.μ G K f x| ≤ A * (holderSemi δ G f).toReal *
      volumeIntegralConstant D.C_D (ν + (δ : ℝ)) * R ^ (ν + (δ : ℝ)) := by
  obtain ⟨hi, hb⟩ := hK.regularized_absolute hδ hf hx
  have hc : 0 ≤ A * (holderSemi δ G f).toReal *
      volumeIntegralConstant D.C_D (ν + (δ : ℝ)) * R ^ (ν + (δ : ℝ)) := by
    have hc := volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D])
      (add_pos_of_nonneg_of_pos hK.kernel.ν_nonneg hδ)
    exact mul_nonneg (mul_nonneg (mul_nonneg hK.kernel.A_nonneg ENNReal.toReal_nonneg) hc.le)
      (Real.rpow_nonneg hK.radius_pos.le _)
  have he : ∫ y in G, |K x y * (f y - f x)| ∂D.μ ≤
      A * (holderSemi δ G f).toReal * volumeIntegralConstant D.C_D (ν + (δ : ℝ)) * R ^ (ν + (δ : ℝ)) := by
    apply (ENNReal.ofReal_le_ofReal_iff hc).mp
    simpa only [← Real.norm_eq_abs, ← ofReal_norm, ofReal_integral_norm_eq_lintegral_enorm hi] using hb
  calc
    _ ≤ ∫ y in G, |K x y * (f y - f x)| ∂D.μ := by
      simpa only [regularizedIntegral, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := D.μ.restrict G) (fun y => K x y * (f y - f x))
    _ ≤ _ := he

end RothschildStein.H2
