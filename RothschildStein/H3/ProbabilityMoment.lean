-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntegralPowerBound
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory

/-- Jensen followed by spatial Fubini. The averaged pth power
is integrable as a consequence of the joint pth moment, rather than a premise. -/
theorem probability_average_moment_bound {α X : Type*}
    [MeasurableSpace α] [MeasurableSpace X]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    {p : ℝ} (hp : 1 ≤ p) {h : α × X → ℝ}
    (hh : AEStronglyMeasurable h (μ.prod ν))
    (hhp : Integrable (fun z => |h z| ^ p) (μ.prod ν))
    (hsection : ∀ᵐ x ∂ν, Integrable (fun t => h (t,x)) μ) :
    Integrable (fun x => |∫ t, h (t,x) ∂μ| ^ p) ν ∧
      (∫ x, |∫ t, h (t,x) ∂μ| ^ p ∂ν) ≤
        ∫ z, |h z| ^ p ∂μ.prod ν := by
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 1).trans hp
  have hm : AEStronglyMeasurable (fun x => ∫ t, h (t,x) ∂μ) ν :=
    hh.prod_swap.integral_prod_right'
  have hmp : AEStronglyMeasurable (fun x => |∫ t, h (t,x) ∂μ| ^ p) ν :=
    (continuous_abs.rpow_const (fun _ => Or.inr hp0)).comp_aestronglyMeasurable hm
  have hb : ∀ᵐ x ∂ν, |∫ t, h (t,x) ∂μ| ^ p ≤ ∫ t, |h (t,x)| ^ p ∂μ := by
    filter_upwards [hsection, hhp.prod_left_ae] with x hx hxp
    exact integral_power_bound_probability μ hp hx hxp
  have hi : Integrable (fun x => |∫ t, h (t,x) ∂μ| ^ p) ν :=
    hhp.integral_prod_right.mono' hmp (hb.mono fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hx)
  refine ⟨hi, ?_⟩
  have hbint := integral_mono_ae hi hhp.integral_prod_right hb
  exact hbint.trans_eq (integral_prod_symm _ hhp).symm

end RothschildStein.H3
