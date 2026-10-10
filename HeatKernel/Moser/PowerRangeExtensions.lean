-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LowerRangeExtensions
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Differentiable extensions for power energy tests

Power derivatives are Lipschitz above a positive lower bound when their exponents are
at most one. This provides global extensions for negative power primitives and for
positive power primitives with exponent at most two.
-/

@[expose] public section

open Set
open scoped NNReal

namespace HeatKernel

/-- A real power of exponent at most one is Lipschitz above a positive lower bound. -/
theorem lipschitzOnWith_rpow_Ici {c q : ℝ} (hc : 0 < c) (hq : q ≤ 1) :
    LipschitzOnWith (Real.toNNReal (|q| * c ^ (q - 1))) (fun x : ℝ => x ^ q) (Ici c) := by
  apply (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x : ℝ => q * x ^ (q - 1))
  · intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hc.trans_le hx)))).hasDerivWithinAt
  · intro x hx
    have hp := Real.rpow_le_rpow_of_nonpos hc hx (sub_nonpos.mpr hq)
    have hn : ‖q * x ^ (q - 1)‖ ≤ |q| * c ^ (q - 1) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (hc.le.trans hx) _)]
      exact mul_le_mul_of_nonneg_left hp (abs_nonneg q)
    have H : ‖q * x ^ (q - 1)‖ ≤ (Real.toNNReal (|q| * c ^ (q - 1)) : ℝ) := by
      simpa only [Real.coe_toNNReal _ (mul_nonneg (abs_nonneg q) (Real.rpow_nonneg hc.le _))] using hn
    exact_mod_cast H

end HeatKernel
