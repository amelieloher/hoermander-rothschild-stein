-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNormalizedEvaluation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Essential mean values at Gaussian endpoint cylinders

A normalized essential quadratic estimate on the inner cylinder controls its
center value. The outer quadratic moment is written as an iterated integral.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
namespace HeatKernel.Gaussian

/-- An essential mean-value estimate gives the squared center value on the
endpoint cylinder. Finiteness of the outer quadratic norm and the essential
estimate are explicit hypotheses. -/
theorem sq_center_le_endpoint_integral_of_essential_bound
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [SFinite μ] [((volume : Measure ℝ).prod μ).IsOpenPosMeasure]
    (s r : ℝ) (w : E) (hr : 0 < r) (f : ℝ × E → ℝ)
    (hf : ContinuousOn f (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ ball w r))
    (hmem : MemLp f 2 ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
      (μ.restrict (ball w (2 * r)))))
    {C : ℝ} (hC : 0 ≤ C) (hV : 0 < μ.real (ball w (2 * r)))
    (hbound : eLpNormEssSup f (((volume : Measure ℝ).prod μ).restrict
      (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ ball w r)) ≤
      ENNReal.ofReal C * eLpNorm f 2
        (ENNReal.ofReal (r ^ 2 * μ.real (ball w (2 * r)))⁻¹ •
          ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
            (μ.restrict (ball w (2 * r)))))) :
    f (s, w) ^ 2 ≤ C ^ 2 / (r ^ 2 * μ.real (ball w (2 * r))) *
      ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
        ∫ z in ball w (2 * r), f (σ, z) ^ 2 ∂μ := by
  have hcenter : (s, w) ∈ Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ ball w r := by
    refine ⟨⟨?_, ?_⟩, mem_ball_self hr⟩ <;> nlinarith [sq_pos_of_pos hr]
  have h := sq_le_normalized_integral_of_essential_bound ((volume : Measure ℝ).prod μ) _
    (isOpen_Ioo.prod isOpen_ball) hf hmem hC (mul_pos (sq_pos_of_pos hr) hV)
    hbound (s, w) hcenter
  rw [integral_prod _ hmem.integrable_sq] at h
  exact h

end HeatKernel.Gaussian
