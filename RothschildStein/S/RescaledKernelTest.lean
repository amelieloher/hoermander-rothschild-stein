-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.RescaledKernelGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The rescaled integration kernel is an actual test function
on Ω whenever its closed support ball is interior (BB (2.11), p. 78). -/
def rescaledKernelTest (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) (hx : closedBall x ε ⊆ Ω) :
    TestFunction Ω ℝ (⊤ : ℕ∞) where
  toFun := friedrichsRescaledKernel K.family ε x
  contDiff' := (contDiff_friedrichsRescaledKernel K ε).comp
    (contDiff_const.prodMk contDiff_id)
  hasCompactSupport' := (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
    (tsupport_friedrichsRescaledKernel_subset K hε x)
  tsupport_subset' := (tsupport_friedrichsRescaledKernel_subset K hε x).trans hx

end RothschildStein.S
