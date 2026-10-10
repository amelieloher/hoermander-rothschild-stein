-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NashFromAveraging
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Integral form of the averaging Nash inequality

The L² carrier supplies the triangle inequality. The norm-square identity and
the zero first-moment case are proved here, so the only analytic hypotheses are
the averaging error, the norm bound on the average, and the quadratic energy.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace HeatKernel.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The quadratic moment is the squared norm of the corresponding L² element. -/
theorem integral_sq_eq_norm_toLp_sq {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end HeatKernel.Sobolev
