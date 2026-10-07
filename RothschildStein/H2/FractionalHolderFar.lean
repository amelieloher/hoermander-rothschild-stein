-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalNear

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The far part uses exponent ν−α and the enlarged support radius R+t.
BB Theorem 7.14, p. 305, valid also when α equals the kernel smoothness exponent. -/
theorem SupportedKernel.fractional_far_le {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    {α : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hαν : α < ν)
    {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) (hxx : x₀ ≠ x)
    (hκ : dist x₀ x < D.κ / 3) :
    |∫ y in G ∩ {y | 2 * dist x₀ x < dist x₀ y}, (K x₀ y - K x y) * f y ∂D.μ| ≤
      S * M * dist x₀ x ^ α * volumeIntegralConstant D.C_D (ν - α) *
        (R + dist x₀ x) ^ (ν - α) := by
  classical
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  let F : Set X := {y | 2 * t < dist x₀ y}
  have hF : MeasurableSet F := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  let g : X → ℝ := F.indicator (fun y => (K x₀ y - K x y) * f y)
  have hi : IntegrableOn g G D.μ := by
    have hi₀ := (hK.fractional_absolute (hα.trans hαν) hf hM hfb hx₀).1
    have hi₁ := (hK.fractional_absolute (hα.trans hαν) hf hM hfb hx).1
    have he : (fun y => (K x₀ y - K x y) * f y) =
        (fun y => K x₀ y * f y - K x y * f y) := by funext y; ring
    dsimp only [g]
    rw [he]
    exact (hi₀.sub hi₁).indicator hF
  have hr : 0 < R + t := add_pos hK.radius_pos ht
  have hrκ : R + t ≤ 6 * D.κ := by linarith [hK.radius_le, D.κ_pos]
  have hC : 0 ≤ S * M * t ^ α := mul_nonneg (mul_nonneg hK.kernel.S_nonneg hM) (Real.rpow_nonneg ht.le _)
  have hb := D.outerPatch.lintegral_abs_le_inner (hK.sub_G (hK.sub_EG hx₀))
    hK.kernel.measurable_E hr hrκ (sub_pos.mpr hαν) hC (g := g) (by
      intro y hy hry
      by_cases hyF : y ∈ F
      swap
      · exact indicator_of_notMem hyF _
      rw [show g y = (K x₀ y - K x y) * f y from indicator_of_mem hyF _]
      have hd : R ≤ dist x y := by
        have htri := dist_triangle x₀ x y
        change R + dist x₀ x ≤ dist x₀ y at hry
        linarith
      rw [hK.support x₀ hx₀ y hy (by linarith), hK.support x hx y hy hd,
        sub_self, zero_mul]) (by
      filter_upwards [ae_restrict_mem hK.kernel.measurable_E, hfb] with y hy hfy
      intro hxy
      by_cases hyF : y ∈ F
      swap
      · simp only [g, indicator_of_notMem hyF, abs_zero]
        exact mul_nonneg hC (kernelWeight_nonneg _ _ _ _)
      rw [show g y = (K x₀ y - K x y) * f y from indicator_of_mem hyF _, abs_mul]
      have hs := (hK.kernel.of_le hα hαβ).smooth x₀ (hK.sub_EG hx₀) x (hK.sub_EG hx) y hy hyF
      have he := mul_le_mul hs hfy (abs_nonneg _) (mul_nonneg
        (mul_nonneg hK.kernel.S_nonneg (kernelWeight_nonneg _ _ _ _)) (Real.rpow_nonneg (div_nonneg ht.le dist_nonneg) _))
      refine he.trans_eq ?_
      change S * kernelWeight D.μ ν x₀ y * (t / dist x₀ y) ^ α * M =
        S * M * t ^ α * kernelWeight D.μ (ν - α) x₀ y
      unfold kernelWeight
      rw [Real.div_rpow ht.le dist_nonneg, Real.rpow_sub (dist_pos.mpr hxy)]
      ring)
  have hc : 0 ≤ S * M * t ^ α * volumeIntegralConstant D.C_D (ν - α) * (R + t) ^ (ν - α) :=
    mul_nonneg (mul_nonneg hC
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) (sub_pos.mpr hαν)).le)
      (Real.rpow_nonneg hr.le _)
  have he := abs_integral_le_of_lintegral hi hc hb
  simpa only [g, integral_indicator hF, Measure.restrict_restrict hF, inter_comm] using he

end RothschildStein.H2
