-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Compatible real and nonnegative formulations of weighted chain costs. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal ENNReal BigOperators

namespace HeatKernel

/-- Real power costs on a finite chain coincide with the nonnegative power costs
used in weighted Hölder and shadow summation. -/
theorem ofReal_sum_mul_rpow_eq_coe {ι : Type*} (s : Finset ι)
    (w h : ι → ℝ≥0) (p : ℝ) :
    ENNReal.ofReal ((∑ j ∈ s, (w j : ℝ) * (h j : ℝ)) ^ p) =
      (((∑ j ∈ s, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞) := by
  have heq : ((∑ j ∈ s, w j * h j : ℝ≥0) : ℝ) =
      ∑ j ∈ s, (w j : ℝ) * (h j : ℝ) := by simp
  rw [← heq, ← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]

end HeatKernel
