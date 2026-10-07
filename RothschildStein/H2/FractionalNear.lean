-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalConvergence
public import RothschildStein.H2.IntegralBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The near part of a fractional integral is controlled by the radial volume integral at its center (BB p. 305). -/
theorem SupportedKernel.fractional_near_le {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    (hν : 0 < ν) {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M)
    {x : X} (hx : x ∈ E) {N : Set X} (hN : MeasurableSet N)
    {r : ℝ} (hr : 0 < r) (hrκ : r ≤ 6 * D.κ)
    (hNr : ∀ y ∈ G ∩ N, dist x y < r) :
    |∫ y in G ∩ N, K x y * f y ∂D.μ| ≤
      A * M * volumeIntegralConstant D.C_D ν * r ^ ν := by
  classical
  let g : X → ℝ := N.indicator (fun y => K x y * f y)
  have hi : IntegrableOn g G D.μ :=
    ((hK.fractional_absolute hν hf hM hfb hx).1).indicator hN
  have hb := D.outerPatch.lintegral_abs_le_inner (hK.sub_G (hK.sub_EG hx))
    hK.kernel.measurable_E hr hrκ hν (mul_nonneg hK.kernel.A_nonneg hM)
    (g := g) (by
      intro y hy hyr
      by_cases hyN : y ∈ N
      · exact False.elim ((not_lt_of_ge hyr) (hNr y ⟨hy, hyN⟩))
      · exact indicator_of_notMem hyN _) (by
      filter_upwards [ae_restrict_mem hK.kernel.measurable_E, hfb] with y hy hfy
      intro hxy
      by_cases hyN : y ∈ N
      swap
      · simp only [g, indicator_of_notMem hyN, abs_zero]
        exact mul_nonneg (mul_nonneg hK.kernel.A_nonneg hM) (kernelWeight_nonneg _ _ _ _)
      rw [show g y = K x y * f y from indicator_of_mem hyN _, abs_mul]
      have he := mul_le_mul (hK.kernel.size x (hK.sub_EG hx) y hy hxy) hfy (abs_nonneg _)
        (mul_nonneg hK.kernel.A_nonneg (kernelWeight_nonneg _ _ _ _))
      refine he.trans_eq ?_
      change A * kernelWeight D.μ ν x y * M = A * M * kernelWeight D.μ ν x y
      ring)
  have hc : 0 ≤ A * M * volumeIntegralConstant D.C_D ν * r ^ ν :=
    mul_nonneg (mul_nonneg (mul_nonneg hK.kernel.A_nonneg hM)
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hν).le)
      (Real.rpow_nonneg hr.le _)
  have he := abs_integral_le_of_lintegral hi hc hb
  simpa only [g, integral_indicator hN, Measure.restrict_restrict hN, inter_comm] using he

end RothschildStein.H2
