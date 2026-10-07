-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import RothschildStein.G1.FlowVariational

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A local zero-time flow has identity spatial derivative at its
initial points (BB Lemma 1.52, pp. 30–31). -/
theorem localFlow_fderiv_zero {U : Set E} (hU : IsOpen U)
    (Φ : E × ℝ → E) (hzero : ∀ y ∈ U, Φ (y, 0) = y) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun y => Φ (y, 0)) x = ContinuousLinearMap.id ℝ E := by
  have heq : (fun y => Φ (y, 0)) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hzero y hy
  exact ((hasFDerivAt_id x).congr_of_eventuallyEq heq).fderiv

end RothschildStein.G1
