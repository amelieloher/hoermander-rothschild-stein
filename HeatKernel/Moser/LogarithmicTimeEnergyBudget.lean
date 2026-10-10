-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMeanMonotonicity
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Time integrability and total budget of logarithmic energy -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- A measurable nonnegative logarithmic energy controlled by an absolutely
continuous mean derivative is automatically integrable in time. -/
theorem intervalIntegrable_logarithmic_energy_of_deriv_bound
    {E g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hEm : AEStronglyMeasurable E (volume.restrict (uIcc a b)))
    (hEn : ∀ᵐ t ∂volume, t ∈ uIcc a b → 0 ≤ E t)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * deriv g t) :
    IntervalIntegrable E volume a b := by
  apply (hg.intervalIntegrable_deriv.const_mul 2).mono_fun'
    (hEm.mono_measure (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [ae_restrict_of_ae hEn, ae_restrict_of_ae he,
    ae_restrict_mem measurableSet_uIoc] with t hn ht hm
  rw [Real.norm_eq_abs, abs_of_nonneg (hn (uIoc_subset_uIcc hm))]
  exact ht (uIoc_subset_uIcc hm)

/-- The total logarithmic energy costs at most twice the increase of the corrected
mean; its nonnegative derivative also gives monotonicity on the whole interval. -/
theorem logarithmic_time_energy_budget {E g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hEm : AEStronglyMeasurable E (volume.restrict (uIcc a b)))
    (hEn : ∀ᵐ t ∂volume, t ∈ uIcc a b → 0 ≤ E t)
    (he : ∀ᵐ t ∂volume, t ∈ uIcc a b → E t ≤ 2 * deriv g t) :
    IntervalIntegrable E volume a b ∧ MonotoneOn g (Icc a b) ∧
      (∫ t in a..b, E t) ≤ 2 * (g b - g a) := by
  have hE := intervalIntegrable_logarithmic_energy_of_deriv_bound hg hEm hEn he
  refine ⟨hE, ?_, ?_⟩
  · rw [← uIcc_of_le hab]
    apply monotoneOn_of_absolutelyContinuous_deriv_nonneg hg
    filter_upwards [hEn, he] with t hn ht hm
    linarith [hn hm, ht hm]
  · have H := intervalIntegral.integral_mono_ae_restrict hab hE
      (hg.intervalIntegrable_deriv.const_mul 2) (show E ≤ᵐ[volume.restrict (Icc a b)]
        (fun t => 2 * deriv g t) from by
        filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Icc] with t ht hm
        exact ht (by simpa only [uIcc_of_le hab] using hm))
    rwa [intervalIntegral.integral_const_mul, hg.integral_deriv_eq_sub] at H

end HeatKernel
