-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicEnergyEndpoints
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Reciprocal primitives for absolutely continuous logarithmic mean deviations. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace HeatKernel

/-- The reciprocal primitive integrates the derivative of an absolutely continuous
nonnegative mean deviation, including the nonsmooth time dependence of weak solutions. -/
theorem integral_deriv_div_shift_sq {q : ℝ → ℝ} {a b c : ℝ}
    (hc : 0 < c) (hq : AbsolutelyContinuousOnInterval q a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ q t) :
    (∫ t in a..b, deriv q t / (c + q t)^2) =
      (c + q a)⁻¹ - (c + q b)⁻¹ := by
  have hshift : LipschitzWith 1 (fun t : ℝ => c + t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp
  have hs : AbsolutelyContinuousOnInterval (fun t => c + q t) a b :=
    hshift.comp_absolutelyContinuousOnInterval hq
  have hr : AbsolutelyContinuousOnInterval (fun t => (c + q t)⁻¹) a b :=
    (lipschitzOnWith_inv_Ici hc).comp_absolutelyContinuousOnInterval
      (fun t ht => by change c ≤ c + q t; linarith [hn t ht]) hs
  let F : ℝ → ℝ := fun t => -(c + q t)⁻¹
  have hF : AbsolutelyContinuousOnInterval F a b := hr.neg
  have hd : ∀ᵐ t ∂volume, t ∈ uIoc a b →
      deriv F t = deriv q t / (c + q t)^2 := by
    filter_upwards [hq.ae_differentiableAt] with t ht hmem
    have htc : t ∈ uIcc a b := uIoc_subset_uIcc hmem
    have hne : c + q t ≠ 0 := ne_of_gt (by linarith [hn t htc])
    have hh := (((ht htc).hasDerivAt.const_add c).inv hne).neg
    simpa only [F, Pi.inv_def, Pi.neg_def, neg_div, neg_neg] using hh.deriv
  rw [← intervalIntegral.integral_congr_ae hd, hF.integral_deriv_eq_sub]
  simp only [F]
  ring

end HeatKernel
