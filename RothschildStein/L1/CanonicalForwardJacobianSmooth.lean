-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalForwardJacobian
public import RothschildStein.L1.CanonicalJacobianSmooth
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual forward fibre derivative is the joint derivative with
zero base displacement. -/
theorem forward_fiber_fderiv_apply (C : CanonicalFrameChartData Ω Y x)
    (η u v : Fin N → ℝ) (hq : (η,u) ∈ ball x C.radius ×ˢ ball 0 C.radius) :
    fderiv ℝ (fun z => canonicalFrameMap C.time C.flow (η,z)) u v =
      fderiv ℝ (canonicalFrameMap C.time C.flow) (η,u) (0,v) := by
  have hD := (C.forward_smooth.contDiffAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hq)).differentiableAt (by simp)
  have he := hD.hasFDerivAt.comp u (hasFDerivAt_prodMk_right η u)
  exact congrArg (fun A => A v) he.fderiv

/-- The positive forward volume density is jointly smooth on the actual
base/coefficient patch. -/
theorem forward_abs_jacobian_contDiffOn (C : CanonicalFrameChartData Ω Y x) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
        |(fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (q.1,u)) q.2).det|)
      (ball x C.radius ×ˢ ball 0 C.radius) := by
  have hd := C.forward_smooth.fderiv_of_isOpen (m := (⊤ : ℕ∞)) (isOpen_ball.prod isOpen_ball) (by simp)
  have hm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
        ((fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (q.1,u)) q.2).toLinearMap.toMatrix').det)
      (ball x C.radius ×ˢ ball 0 C.radius) := by
    apply matrixDet_contDiffOn
    intro i j
    have hv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun _ : (Fin N → ℝ) × (Fin N → ℝ) =>
          ((0 : Fin N → ℝ),(Pi.single j (1 : ℝ) : Fin N → ℝ)))
        (ball x C.radius ×ˢ ball 0 C.radius) := contDiffOn_const
    have hh := contDiffOn_pi.mp (hd.clm_apply hv) i
    apply hh.congr
    intro q hq
    change fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (q.1,u)) q.2 (Pi.single j 1) i = _
    exact congrFun (C.forward_fiber_fderiv_apply q.1 q.2 (Pi.single j 1) hq) i
  have he : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
        (fderiv ℝ (fun u => canonicalFrameMap C.time C.flow (q.1,u)) q.2).det)
      (ball x C.radius ×ˢ ball 0 C.radius) := by
    simpa only [LinearMap.det_toMatrix'] using hm
  exact he.abs (fun q hq => abs_pos.mp (C.forward_abs_jacobian_pos q.1 q.2 hq.1 hq.2))
end CanonicalFrameChartData
end RothschildStein.L1
