-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ProbabilityMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory

/-- On a probability space a finite pth moment, p ≥ 1, implies
 integrability of the scalar function. -/
theorem integrable_of_probability_moment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p)
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hm : Integrable (fun x => |f x| ^ p) μ) : Integrable f μ := by
  apply ((integrable_const (1 : ℝ)).add hm).mono' hf
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  by_cases hx : |f x| ≤ 1
  · exact hx.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
  · exact (Real.self_le_rpow_of_one_le (le_of_not_ge hx) hp).trans
      (le_add_of_nonneg_left (by norm_num))

/-- Spatial Jensen and Fubini from the joint moment alone;
 section integrability is derived on the probability parameter space. -/
theorem probability_average_moment_bound_of_moment {α X : Type*}
    [MeasurableSpace α] [MeasurableSpace X]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    {p : ℝ} (hp : 1 ≤ p) {h : α × X → ℝ}
    (hh : AEStronglyMeasurable h (μ.prod ν))
    (hhp : Integrable (fun z => |h z| ^ p) (μ.prod ν)) :
    Integrable (fun x => |∫ t, h (t,x) ∂μ| ^ p) ν ∧
      (∫ x, |∫ t, h (t,x) ∂μ| ^ p ∂ν) ≤ ∫ z, |h z| ^ p ∂μ.prod ν := by
  apply probability_average_moment_bound μ ν hp hh hhp
  filter_upwards [hh.prodMk_right,hhp.prod_left_ae] with x hx hxp
  exact integrable_of_probability_moment μ hp hx hxp

end RothschildStein.H3
