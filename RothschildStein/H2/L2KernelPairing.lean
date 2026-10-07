-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderL2Inner
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- A pair of L² functions has an absolutely convergent product
integral, equal to the inner product of their equivalence classes. -/
theorem l2_kernel_pairing {μ : Measure X} {k f : X → ℝ}
    (hk : MemLp k 2 μ) (hf : MemLp f 2 μ) :
    Integrable (fun x => k x * f x) μ ∧
      (∫ x, k x * f x ∂μ) = inner ℝ (hk.toLp k) (hf.toLp f) := by
  constructor
  · exact memLp_one_iff_integrable.mp (hk.fun_mul hf)
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk.coeFn_toLp, hf.coeFn_toLp] with x hx hy
    rw [Real.inner_apply, hx, hy]

end RothschildStein.H2
