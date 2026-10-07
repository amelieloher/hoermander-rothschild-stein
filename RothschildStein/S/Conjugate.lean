-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology ENNReal
namespace RothschildStein.S

/-- A Hölder conjugate exists for every extended exponent p ≥ 1,
including both endpoints (BB pp. 68–69). -/
theorem holderConjugate_complement (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ENNReal.HolderConjugate p ((1 - p⁻¹)⁻¹) := by
  apply ENNReal.holderConjugate_iff.mpr
  simp only [inv_inv]
  exact add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr hp)

end RothschildStein.S
