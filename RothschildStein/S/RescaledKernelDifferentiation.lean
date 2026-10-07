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

/-- Differentiation of the local Friedrichs operator is justified
by its common interior compact support and local integrability alone
(BB p. 78; differentiation). -/
theorem fderiv_friedrichsKernelOp_apply_of_interior_ball
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (x v : Fin n → ℝ)
    (hx : closedBall x (ε+r) ⊆ Ω) :
    fderiv ℝ (friedrichsKernelOp K.family h ε) x v =
      ∫ z, h z * fderiv ℝ (uncurry (friedrichsRescaledKernel K.family ε)) (x,z) (v,0) := by
  have he : friedrichsKernelOp K.family h ε =
      fun a => ∫ z, h z * friedrichsRescaledKernel K.family ε a z := by
    funext a
    exact friedrichsKernelOp_eq_rescaled K.family h hε a
  rw [he]
  exact fderiv_compactKernelIntegral_apply_of_local_data Ω
    ⟨closedBall x (ε+r),isCompact_closedBall x (ε+r)⟩ hx
    (contDiff_friedrichsRescaledKernel K ε) hh x v hr
    (fun a z ha hz => friedrichsRescaledKernel_eq_zero_of_notMem_common_ball K hε x a z ha hz)

end RothschildStein.S
