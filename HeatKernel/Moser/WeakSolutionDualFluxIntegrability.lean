-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Integrability of dual flux evaluations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
namespace HeatKernel

/-- Square-integrable dual and test curves have an integrable evaluation pairing. -/
theorem integrable_dual_apply_of_memLp_two {α E : Type*}
    [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : α → (E →L[ℝ] ℝ)} {v : α → E} (hF : MemLp F 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun t => F t (v t)) μ := by
  let D := ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)
  exact memLp_one_iff_integrable.mp (D.memLp_of_bilin 1 hF hv)

end HeatKernel
