-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalForwardJacobian
public import RothschildStein.L1.CanonicalBasisAssembly
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual forward chart derivative at the origin is the original
frame, so the density normalization retains the frame determinant. -/
theorem forward_hasFDerivAt_zero (C : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (η : Fin N → ℝ) (hη : η ∈ ball x C.radius) :
    HasFDerivAt (fun u => canonicalFrameMap C.time C.flow (η,u)) (frameValueCLM Y η) 0 := by
  have h0 : (0 : Fin N → ℝ) ∈ ball 0 C.radius := mem_ball_self C.radius_pos
  have hηi := ball_subset_ball C.radius_le_initial hη
  have ht : C.time ∈ Ioo (-C.timeRadius) C.timeRadius :=
    ⟨by linarith [C.time_pos,C.timeRadius_pos],C.time_lt⟩
  have hη0 : ((0 : Fin N → ℝ),η) ∈ ball (0,x) C.initialRadius := by
    simpa only [smul_zero] using (C.coefficients (η,0) ⟨hη,h0⟩).1
  exact canonicalFrameMap_coefficients_hasFDerivAt_of_flow hΩ isOpen_ball
    C.timeRadius_pos (ne_of_gt C.time_pos) ht Y hY C.flow C.flow_smooth
    (fun q hq => (C.flow_ode q hq).1) (fun q hq t ht =>
      ⟨((C.flow_ode q hq).2 t ht).2,((C.flow_ode q hq).2 t ht).1⟩)
    η hη0 (fun t ht => C.flow_zero η hηi t ht)

/-- The positive normalization factor is exactly the absolute original
frame determinant, rather than its possibly negative oriented value. -/
theorem forward_abs_jacobian_zero (C : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (η : Fin N → ℝ) (hη : η ∈ ball x C.radius) :
    |(fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (η,u)) 0).det| =
      |(frameValueCLM Y η).det| := by
  rw [(C.forward_hasFDerivAt_zero hΩ hY η hη).fderiv]
end CanonicalFrameChartData
end RothschildStein.L1
