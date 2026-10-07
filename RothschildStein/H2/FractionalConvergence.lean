-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.AbsoluteConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
/-- Transfer ae strong measurability to the input subtype. -/
theorem aestronglyMeasurable_subtype_of_restrict {μ : Measure X} {G : Set X} {f : X → ℝ}
    (hG : MeasurableSet G) (hf : AEStronglyMeasurable f (μ.restrict G)) :
    AEStronglyMeasurable (fun y : G => f y) (μ.comap Subtype.val) := by
  apply (MeasurableEmbedding.subtype_coe hG).aestronglyMeasurable_map_iff.mp
  simpa only [map_comap_subtype_coe hG] using hf

/-- Absolute convergence for a fractional kernel acting on an ae bounded
input, with the explicit sup bound. BB Theorem 7.14, p. 305. -/
theorem SupportedKernel.fractional_absolute {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    (hν : 0 < ν) {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M)
    {x : X} (hx : x ∈ E) :
    IntegrableOn (fun y => K x y * f y) G D.μ ∧
      (∫⁻ y in G, ENNReal.ofReal |K x y * f y| ∂D.μ) ≤
        ENNReal.ofReal (A * M * volumeIntegralConstant D.C_D ν * R ^ ν) := by
  have hxG := hK.sub_EG hx
  have hbound := D.outerPatch.lintegral_abs_le_inner (hK.sub_G hxG) hK.kernel.measurable_E
    hK.radius_pos (hK.radius_le.trans (by change 3 * D.κ ≤ 6 * D.κ; have := D.κ_pos; linarith))
    hν (mul_nonneg hK.kernel.A_nonneg hM) (g := fun y => K x y * f y)
    (fun y hy hr => by rw [hK.support x hx y hy hr, zero_mul]) (by
      filter_upwards [ae_restrict_mem hK.kernel.measurable_E, hfb] with y hy hfy
      intro hxy
      rw [abs_mul]
      have he := mul_le_mul (hK.kernel.size x hxG y hy hxy) hfy (abs_nonneg _) (by
        exact mul_nonneg hK.kernel.A_nonneg (kernelWeight_nonneg _ _ _ _))
      refine he.trans_eq ?_
      change A * kernelWeight D.μ ν x y * M = A * M * kernelWeight D.μ ν x y
      ring)
  refine ⟨integrableOn_of_subtype_lintegral hK.kernel.measurable_E ?_
    (hbound.trans_lt ENNReal.ofReal_lt_top), hbound⟩
  exact (hK.kernel.measurable_slice hxG).aestronglyMeasurable.mul
    (aestronglyMeasurable_subtype_of_restrict hK.kernel.measurable_E hf)

/-- The pointwise fractional-integral sup bound, BB p. 305. -/
theorem SupportedKernel.fractional_abs_le {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    (hν : 0 < ν) {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M)
    {x : X} (hx : x ∈ E) :
    |fractionalIntegral D.μ G K f x| ≤ A * M * volumeIntegralConstant D.C_D ν * R ^ ν := by
  obtain ⟨hi, hb⟩ := hK.fractional_absolute hν hf hM hfb hx
  have hc : 0 ≤ A * M * volumeIntegralConstant D.C_D ν * R ^ ν :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.kernel.A_nonneg hM)
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hν).le)
      (Real.rpow_nonneg hK.radius_pos.le _)
  have he : ∫ y in G, |K x y * f y| ∂D.μ ≤ A * M * volumeIntegralConstant D.C_D ν * R ^ ν := by
    apply (ENNReal.ofReal_le_ofReal_iff hc).mp
    simpa only [← Real.norm_eq_abs, ← ofReal_norm, ofReal_integral_norm_eq_lintegral_enorm hi] using hb
  calc
    _ ≤ ∫ y in G, |K x y * f y| ∂D.μ := by
      simpa only [fractionalIntegral, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := D.μ.restrict G) (fun y => K x y * f y)
    _ ≤ _ := he

end RothschildStein.H2
