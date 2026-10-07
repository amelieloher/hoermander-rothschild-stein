-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeCanonicalCharts
public import RothschildStein.L1.CanonicalChartIdentities
public import RothschildStein.L1.CanonicalBracketAssembly
public import RothschildStein.L1.CanonicalSmoothLocalCharts
public import RothschildStein.L1.CanonicalChartSmallPatch
public import RothschildStein.L1.CanonicalExponential
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual coefficient exponential remains in the original field domain. -/
theorem forward_mem (D : CanonicalFrameChartData Ω Y x)
    {q : (Fin N → ℝ) × (Fin N → ℝ)}
    (hq : q ∈ ball x D.radius ×ˢ ball 0 D.radius) :
    canonicalFrameMap D.time D.flow q ∈ Ω := by
  exact ((D.flow_ode (D.time⁻¹ • q.2,q.1) (D.coefficients q hq).1).2
    D.time ⟨by linarith [D.timeRadius_pos, D.time_pos], D.time_lt⟩).2

/-- Differentiating the second variable equals the total joint derivative
applied to a vector with zero first component. -/
theorem theta_fiber_fderiv_apply (D : CanonicalFrameChartData Ω Y x)
    (η ξ v : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain) :
    fderiv ℝ (fun z => D.theta (η,z)) ξ v = fderiv ℝ D.theta (η,ξ) (0,v) := by
  have hD := (D.theta_smooth.contDiffAt (D.inverseDomain_open.mem_nhds hq)).differentiableAt (by simp)
  have he := hD.hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right η ξ)
  exact congrArg (fun A => A v) he.fderiv

/-- The actual pulled-back field is jointly
smooth in the base point and canonical coordinate on the common patch. -/
theorem pullbackField_contDiffOn_joint (D : CanonicalFrameChartData Ω Y x)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : (Fin N → ℝ) × (Fin N → ℝ) => D.pullbackField q.1 V q.2)
      (ball x D.radius ×ˢ ball 0 D.radius) := by
  have hm := contDiffOn_fst.prodMk D.forward_smooth
  have hΘ := (D.theta_smooth.fderiv_of_isOpen D.inverseDomain_open (by simp)).comp hm
    (fun q hq => (D.coefficients q hq).2.1)
  have hv := hV.comp D.forward_smooth (fun q hq => D.forward_mem hq)
  have hz : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => (0 : Fin N → ℝ))
      (ball x D.radius ×ˢ ball 0 D.radius) := contDiffOn_const
  have h := hΘ.clm_apply (hz.prodMk hv)
  apply h.congr
  intro q hq
  exact D.theta_fiber_fderiv_apply q.1 (canonicalFrameMap D.time D.flow q)
    (V (canonicalFrameMap D.time D.flow q)) (D.coefficients q hq).2.1
end CanonicalFrameChartData
end RothschildStein.L1
