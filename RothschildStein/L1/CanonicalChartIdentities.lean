-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartData
public import RothschildStein.L1.CanonicalBasisAssembly
public import RothschildStein.L1.CanonicalRadialAssembly
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual pulled-back tangent frame in the chosen canonical chart. -/
def coordinateField (D : CanonicalFrameChartData Ω Y x) (η : Fin N → ℝ)
    (i : Fin N) (u : Fin N → ℝ) : Fin N → ℝ :=
  coordinatePullbackField Y (fun ξ => D.theta (η,ξ))
    (fun v => canonicalFrameMap D.time D.flow (η,v)) i u

/-- All diagonal points of the common base patch map to zero. -/
theorem theta_diagonal (D : CanonicalFrameChartData Ω Y x)
    (η : Fin N → ℝ) (hη : η ∈ ball x D.radius) : D.theta (η,η) = 0 := by
  have h0 : (0 : Fin N → ℝ) ∈ ball 0 D.radius := mem_ball_self D.radius_pos
  have he := (D.coefficients (η,0) ⟨hη,h0⟩).2.2
  have ht : D.time ∈ Ioo (-D.timeRadius) D.timeRadius :=
    ⟨by linarith [D.time_pos,D.timeRadius_pos],D.time_lt⟩
  have hk : canonicalFrameMap D.time D.flow (η,0) = η := by
    simpa [canonicalFrameMap] using D.flow_zero η
      (ball_subset_ball D.radius_le_initial hη) D.time ht
  rwa [hk] at he

/-- The actual coordinate frame has the Euler radial identity
throughout the common coefficient neighborhood. -/
theorem radial_identity (D : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (η u : Fin N → ℝ) (hη : η ∈ ball x D.radius) (hu : u ∈ ball 0 D.radius) :
    ∑ i, u i • D.coordinateField η i u = u := by
  have hq := D.coefficients (η,u) ⟨hη,hu⟩
  exact canonicalPullback_radial_identity_of_flow hΩ isOpen_ball D.inverseDomain_open
    (isOpen_ball.prod isOpen_ball) D.time_pos D.time_lt Y hY D.flow D.flow_ode
    D.theta D.theta_smooth (fun q hq => (D.coefficients q hq).2.2) η u ⟨hη,hu⟩ hq.1 hq.2.1

/-- Every base point in the chosen patch has the standard
coordinate frame values at zero. -/
theorem basis_values (D : CanonicalFrameChartData Ω Y x)
    (hΩ : IsOpen Ω) (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (η : Fin N → ℝ) (hη : η ∈ ball x D.radius) (i : Fin N) :
    D.coordinateField η i 0 = Pi.single i (1 : ℝ) := by
  have h0 : (0 : Fin N → ℝ) ∈ ball 0 D.radius := mem_ball_self D.radius_pos
  have hηi := ball_subset_ball D.radius_le_initial hη
  have ht : D.time ∈ Ioo (-D.timeRadius) D.timeRadius :=
    ⟨by linarith [D.time_pos,D.timeRadius_pos],D.time_lt⟩
  have hη0 : ((0 : Fin N → ℝ),η) ∈ ball (0,x) D.initialRadius := by
    simpa only [smul_zero] using (D.coefficients (η,0) ⟨hη,h0⟩).1
  have hk : canonicalFrameMap D.time D.flow (η,0) = η := by
    simpa [canonicalFrameMap] using D.flow_zero η hηi D.time ht
  have hθ : DifferentiableAt ℝ (fun ξ => D.theta (η,ξ)) η :=
    ((D.theta_smooth.contDiffAt (D.inverseDomain_open.mem_nhds
      (D.basePatch_subset ⟨hη,hη⟩))).comp η
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hd := canonicalFrameMap_coefficients_hasFDerivAt_of_flow hΩ isOpen_ball
    D.timeRadius_pos (ne_of_gt D.time_pos) ht Y hY D.flow D.flow_smooth
    (fun q hq => (D.flow_ode q hq).1) (fun q hq t ht =>
      ⟨((D.flow_ode q hq).2 t ht).2,((D.flow_ode q hq).2 t ht).1⟩)
    η hη0 (fun t ht => D.flow_zero η hηi t ht)
  have hinv : (fun v => D.theta (η,canonicalFrameMap D.time D.flow (η,v))) =ᶠ[𝓝 0] id := by
    have hc : ContinuousAt (fun v : Fin N → ℝ => (η,v)) 0 :=
      continuousAt_const.prodMk continuousAt_id
    have hm : ∀ᶠ v in 𝓝 (0 : Fin N → ℝ), (η,v) ∈ ball x D.radius ×ˢ ball 0 D.radius := hc.preimage_mem_nhds ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hη,h0⟩)
    exact hm.mono (fun v hv => (D.coefficients (η,v) hv).2.2)
  exact coordinatePullbackField_basis_values Y (fun ξ => D.theta (η,ξ))
    (fun v => canonicalFrameMap D.time D.flow (η,v)) η hk hθ hd hinv i
end CanonicalFrameChartData
end RothschildStein.L1
