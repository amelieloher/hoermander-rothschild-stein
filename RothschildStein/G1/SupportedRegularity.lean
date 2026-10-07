-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Const

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace RothschildStein.G1

/-- A function smooth on an open set containing its closed support
is globally smooth at the same order. This is the zero-extension regularity
step, and works in particular for C¹ (BB Prop 2.18(i), pp. 84–85). -/
theorem contDiff_of_supported_contDiffOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Set E} (hB : IsOpen B) {f : E → F} {n : ℕ∞ω}
    (hf : ContDiffOn ℝ n f B) (hsupp : tsupport f ⊆ B) : ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ B
  · exact hf.contDiffAt (hB.mem_nhds hx)
  · have heq := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsupp h))
    exact contDiffAt_const.congr_of_eventuallyEq heq

end RothschildStein.G1
