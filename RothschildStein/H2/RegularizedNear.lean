-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.PrincipalValueLimits
public import RothschildStein.H2.IntegralBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The near regularized integral is controlled at its own center.
BB Theorem 7.12, pp. 303–304; closed near regions are included. -/
theorem SupportedKernel.regularized_near_le {D : LocDoubling X} {E G : Set X}
    {β A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    {δ : ℝ≥0} (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x : X} (hx : x ∈ E) {N : Set X} (hN : MeasurableSet N)
    {r : ℝ} (hr : 0 < r) (hrκ : r ≤ 6 * D.κ)
    (hNr : ∀ y ∈ G ∩ N, dist x y < r) :
    |∫ y in G ∩ N, K x y * (f y - f x) ∂D.μ| ≤
      A * (holderSemi δ G f).toReal * volumeIntegralConstant D.C_D δ * r ^ (δ : ℝ) := by
  classical
  let g : X → ℝ := N.indicator (fun y => K x y * (f y - f x))
  have hi : IntegrableOn g G D.μ :=
    ((hK.regularized_absolute hδ hf hx).1).indicator hN
  have hb := D.outerPatch.lintegral_abs_le_inner (hK.sub_G (hK.sub_EG hx))
    hK.kernel.measurable_E (C := A * (holderSemi δ G f).toReal) hr hrκ (show 0 < (δ : ℝ) from hδ) (mul_nonneg hK.kernel.A_nonneg ENNReal.toReal_nonneg)
    (g := g) (by
      intro y hy hyr
      by_cases hyN : y ∈ N
      · exact False.elim ((not_lt_of_ge hyr) (hNr y ⟨hy, hyN⟩))
      · exact indicator_of_notMem hyN _) (by
      filter_upwards [ae_restrict_mem hK.kernel.measurable_E] with y hy
      intro hxy
      by_cases hyN : y ∈ N
      swap
      · simp only [g, indicator_of_notMem hyN, abs_zero]
        exact mul_nonneg (mul_nonneg hK.kernel.A_nonneg ENNReal.toReal_nonneg) (kernelWeight_nonneg _ _ _ _)
      rw [show g y = K x y * (f y - f x) from indicator_of_mem hyN _, abs_mul]
      have hfy := sub_le_holderSemi hf.parts.2 hy (hK.sub_EG hx)
      rw [dist_comm y x] at hfy
      have he := mul_le_mul (hK.kernel.size x (hK.sub_EG hx) y hy hxy) hfy (abs_nonneg _)
        (mul_nonneg hK.kernel.A_nonneg (kernelWeight_nonneg _ _ _ _))
      refine he.trans_eq ?_
      change A * kernelWeight D.μ 0 x y * ((holderSemi δ G f).toReal * dist x y ^ (δ : ℝ)) =
        A * (holderSemi δ G f).toReal * kernelWeight D.μ (δ : ℝ) x y
      unfold kernelWeight
      rw [Real.rpow_zero]
      ring)
  have hc : 0 ≤ A * (holderSemi δ G f).toReal * volumeIntegralConstant D.C_D δ * r ^ (δ : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.kernel.A_nonneg ENNReal.toReal_nonneg)
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) (show 0 < (δ : ℝ) from hδ)).le)
      (Real.rpow_nonneg hr.le _)
  have he := abs_integral_le_of_lintegral hi hc hb
  simpa only [g, integral_indicator hN, Measure.restrict_restrict hN, inter_comm] using he

end RothschildStein.H2
