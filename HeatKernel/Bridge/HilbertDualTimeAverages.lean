-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalTimeAverages
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-! Local strong time averaging in Hilbert spaces and their continuous duals. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HeatKernel

/-- The operator norm on the real continuous dual of a Hilbert space is induced
by an inner product, as follows from the Riesz isometry and the parallelogram law. -/
@[instance_reducible]
def hilbertDualInnerProductSpace (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InnerProductSpace ℝ (E →L[ℝ] ℝ) :=
  InnerProductSpace.ofNorm ℝ (E := E →L[ℝ] ℝ) (fun D F => by
    let R := (InnerProductSpace.toDual ℝ E).symm
    have h := parallelogram_law_with_norm_mul ℝ (R D) (R F)
    simpa only [← R.map_add, ← R.map_sub, R.norm_map] using h)

end HeatKernel
