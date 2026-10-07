-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory

/-- Jensen's power estimate for a probability measure. This is
the normalized weighted-remainder estimate, including p=1. -/
theorem integral_power_bound_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 ≤ p)
    {h : α → ℝ} (hh : Integrable h μ)
    (hhp : Integrable (fun x => |h x| ^ p) μ) :
    |∫ x, h x ∂μ| ^ p ≤ ∫ x, |h x| ^ p ∂μ := by
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 1).trans hp
  have hj := (convexOn_rpow hp).map_integral_le
    (continuousOn_id.rpow_const (fun _ _ => Or.inr hp0)) isClosed_Ici
    (Filter.Eventually.of_forall fun x => abs_nonneg (h x))
    hh.abs hhp
  have hi : |∫ x, h x ∂μ| ≤ ∫ x, |h x| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h
  exact (Real.rpow_le_rpow (abs_nonneg _) hi hp0).trans hj

end RothschildStein.H3
