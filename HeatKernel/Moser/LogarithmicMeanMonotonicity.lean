-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMeanPrimitive

/-! Monotonicity of the corrected weighted logarithmic mean. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace HeatKernel

/-- A nonnegative almost everywhere derivative makes an absolutely continuous mean
nondecreasing throughout its time interval. -/
theorem monotoneOn_of_absolutelyContinuous_deriv_nonneg {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hd : ∀ᵐ t ∂volume, t ∈ uIcc a b → 0 ≤ deriv g t) :
    MonotoneOn g (uIcc a b) := by
  intro x hx y hy hxy
  have hsub := uIcc_subset_uIcc hx hy
  have hnonneg : 0 ≤ ∫ t in x..y, deriv g t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hxy
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc] with t ht hm
    exact ht (hsub (Icc_subset_uIcc hm))
  rw [(hg.mono hsub).integral_deriv_eq_sub] at hnonneg
  linarith

/-- The linear correction of a logarithmic mean is monotone and controls its energy
whenever the mean obeys the logarithmic differential inequality almost everywhere. -/
theorem logarithmic_mean_correction {m E : ℝ → ℝ} {a b C : ℝ}
    (hm : AbsolutelyContinuousOnInterval m a b)
    (hE : ∀ᵐ t ∂volume, t ∈ uIcc a b → 0 ≤ E t)
    (hineq : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t / 2 - C ≤ deriv m t) :
    AbsolutelyContinuousOnInterval (fun t => m t + C * t) a b ∧
      MonotoneOn (fun t => m t + C * t) (uIcc a b) ∧
      ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * deriv (fun s => m s + C * s) t := by
  have hlin : ContDiff ℝ 1 (fun t : ℝ => C * t) := contDiff_const.mul contDiff_id
  have hg : AbsolutelyContinuousOnInterval (fun t => m t + C * t) a b :=
    hm.add hlin.contDiffOn.absolutelyContinuousOnInterval
  have hder : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      deriv (fun s => m s + C * s) t = deriv m t + C := by
    filter_upwards [hm.ae_differentiableAt] with t ht hmem
    have H := (ht hmem).hasDerivAt.add ((hasDerivAt_id t).const_mul C)
    simpa only [Pi.add_def, id_eq, mul_one] using H.deriv
  have hbound : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      E t ≤ 2 * deriv (fun s => m s + C * s) t := by
    filter_upwards [hineq, hder] with t ht hd hmem
    rw [hd hmem]
    linarith [ht hmem]
  refine ⟨hg, monotoneOn_of_absolutelyContinuous_deriv_nonneg hg ?_, hbound⟩
  filter_upwards [hE, hbound] with t ht hb hmem
  linarith [ht hmem, hb hmem]

end HeatKernel
