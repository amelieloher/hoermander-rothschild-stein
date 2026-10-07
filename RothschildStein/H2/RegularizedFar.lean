-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.RegularizedNear
public import RothschildStein.H2.OuterDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The far smoothness term A₁₁ is absolutely integrable and has
its explicit Hölder bound. BB p. 303; no cancellation is used in this term. -/
theorem SupportedKernel.regularized_far_smooth {D : LocDoubling X} {E G : Set X}
    {β A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) (hxx : x₀ ≠ x)
    (hκ : dist x₀ x < D.κ / 3) :
    IntegrableOn (fun y => (K x y - K x₀ y) * (f y - f x₀))
      (G ∩ {y | 2 * dist x₀ x < dist x₀ y}) D.μ ∧
    |∫ y in G ∩ {y | 2 * dist x₀ x < dist x₀ y}, (K x y - K x₀ y) * (f y - f x₀) ∂D.μ| ≤
      volumeIntegralConstant D.C_D (β - δ) * S * (holderSemi δ G f).toReal * dist x₀ x ^ (δ : ℝ) := by
  classical
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  let F : Set X := {y | 2 * t < dist x₀ y}
  have hF : MeasurableSet F := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  let g : X → ℝ := F.indicator (fun y => (K x y - K x₀ y) * (f y - f x₀))
  have hC : 0 ≤ S * (holderSemi δ G f).toReal * t ^ β :=
    mul_nonneg (mul_nonneg hK.kernel.S_nonneg ENNReal.toReal_nonneg) (Real.rpow_nonneg ht.le β)
  have hb := D.outerPatch.lintegral_abs_le_outer (hK.sub_G (hK.sub_EG hx₀))
    hK.kernel.measurable_E (sub_pos.mpr hδβ) (a := 2 * t) (b := R + 3 * t)
    (by linarith) (by linarith [hK.radius_pos])
    (by change R + 3 * t ≤ 6 * D.κ; dsimp [t]; linarith [hK.radius_le, D.κ_pos]) hC
    (g := g) (by
      intro y hy hry
      by_cases hyF : y ∈ F
      swap
      · exact indicator_of_notMem hyF _
      rw [show g y = (K x y - K x₀ y) * (f y - f x₀) from indicator_of_mem hyF _]
      rcases hry with hry | hry
      · have hfy : 2 * t < dist x₀ y := hyF
        linarith
      · have htri := dist_triangle x₀ x y
        change R + 3 * dist x₀ x ≤ dist x₀ y at hry
        rw [hK.support x₀ hx₀ y hy (by linarith), hK.support x hx y hy (by linarith), sub_self, zero_mul]) (by
      filter_upwards [ae_restrict_mem hK.kernel.measurable_E] with y hy
      intro hya
      by_cases hyF : y ∈ F
      swap
      · simp only [g, indicator_of_notMem hyF, abs_zero]
        exact mul_nonneg hC (kernelWeight_nonneg _ _ _ _)
      rw [show g y = (K x y - K x₀ y) * (f y - f x₀) from indicator_of_mem hyF _, abs_mul]
      have hs := hK.kernel.smooth x₀ (hK.sub_EG hx₀) x (hK.sub_EG hx) y hy hyF
      rw [abs_sub_comm] at hs
      have hf' := sub_le_holderSemi hf.parts.2 hy (hK.sub_EG hx₀)
      rw [dist_comm y x₀] at hf'
      have he := mul_le_mul hs hf' (abs_nonneg _) (mul_nonneg
        (mul_nonneg hK.kernel.S_nonneg (kernelWeight_nonneg _ _ _ _))
          (Real.rpow_nonneg (div_nonneg ht.le dist_nonneg) β))
      refine he.trans_eq ?_
      change S * kernelWeight D.μ 0 x₀ y * (t / dist x₀ y) ^ β *
        ((holderSemi δ G f).toReal * dist x₀ y ^ (δ : ℝ)) =
        S * (holderSemi δ G f).toReal * t ^ β * kernelWeight D.μ (-(β - δ)) x₀ y
      have hd : 0 < dist x₀ y := by have hfy : 2 * t < dist x₀ y := hyF; linarith
      unfold kernelWeight
      rw [Real.rpow_zero, Real.div_rpow ht.le hd.le]
      rw [show -(β - (δ : ℝ)) = (δ : ℝ) - β by ring, Real.rpow_sub hd]
      ring)
  have hi : IntegrableOn g G D.μ := integrableOn_of_subtype_lintegral hK.kernel.measurable_E
    ((((hK.kernel.measurable_slice (hK.sub_EG hx)).sub (hK.kernel.measurable_slice (hK.sub_EG hx₀))).mul
      ((hf.measurable_subtype hδ).sub measurable_const)).aestronglyMeasurable.indicator
        (hF.preimage measurable_subtype_coe)) (hb.trans_lt ENNReal.ofReal_lt_top)
  have hc : 0 ≤ S * (holderSemi δ G f).toReal * t ^ β *
      volumeIntegralConstant D.C_D (β - δ) * (2 * t) ^ (-(β - δ)) :=
    mul_nonneg (mul_nonneg hC
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) (sub_pos.mpr hδβ)).le)
      (Real.rpow_nonneg (by linarith) _)
  have he := abs_integral_le_of_lintegral hi hc hb
  have hp : t ^ β * (2 * t) ^ (-(β - (δ : ℝ))) ≤ t ^ (δ : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le]
    have hid : t ^ β * (2 ^ (-(β - (δ : ℝ))) * t ^ (-(β - (δ : ℝ)))) =
        2 ^ (-(β - (δ : ℝ))) * t ^ (δ : ℝ) := by
      rw [mul_left_comm, ← Real.rpow_add ht]
      rw [show β + -(β - (δ : ℝ)) = (δ : ℝ) by ring]
    rw [hid]
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith))
      (Real.rpow_nonneg ht.le (δ : ℝ))).trans_eq (one_mul _)
  have hc' : 0 ≤ volumeIntegralConstant D.C_D (β - δ) * S * (holderSemi δ G f).toReal := mul_nonneg (mul_nonneg
    (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) (sub_pos.mpr hδβ)).le
    hK.kernel.S_nonneg) ENNReal.toReal_nonneg
  have he' := mul_le_mul_of_nonneg_left hp hc'
  refine ⟨by simpa only [g, inter_comm] using (integrableOn_indicator_iff hF).mp hi, ?_⟩
  have hres : |∫ y in G ∩ F, (K x y - K x₀ y) * (f y - f x₀) ∂D.μ| ≤
      S * (holderSemi δ G f).toReal * t ^ β * volumeIntegralConstant D.C_D (β - δ) * (2 * t) ^ (-(β - δ)) := by
    simpa only [g, integral_indicator hF, Measure.restrict_restrict hF, inter_comm] using he
  dsimp [t] at hres he'
  nlinarith

end RothschildStein.H2
