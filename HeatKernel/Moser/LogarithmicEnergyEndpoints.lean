-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LowerRangeExtensions
public import HeatKernel.Moser.BoundedTimeAverages
public import HeatKernel.Moser.NonlinearEnergyDifferentiability
public import HeatKernel.Moser.TimeAverageDerivatives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Logarithmic energy endpoint identities above a positive lower bound

The reciprocal is Lipschitz on a positive half-line, with constant given by the inverse
square of its lower endpoint. The scalar extension transfers the weighted energy identity
to the logarithm on that range.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- The reciprocal has Lipschitz constant at most the inverse square of a positive lower bound. -/
theorem lipschitzOnWith_inv_Ici {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith (Real.toNNReal ((c ^ 2)⁻¹)) (fun x : ℝ => x⁻¹) (Ici c) := by
  apply (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x : ℝ => -(x ^ 2)⁻¹)
  · intro x hx
    exact (hasDerivAt_inv (ne_of_gt (hc.trans_le hx))).hasDerivWithinAt
  · intro x hx
    have hsq : c ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hc.le hx 2
    have hi : (x ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hc) hsq
    have hn : ‖-(x ^ 2)⁻¹‖ ≤ (c ^ 2)⁻¹ := by
      simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x))] using hi
    have H : ‖-(x ^ 2)⁻¹‖ ≤ (Real.toNNReal ((c ^ 2)⁻¹) : ℝ) := by
      simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg c))] using hn
    exact_mod_cast H

end HeatKernel
