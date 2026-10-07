-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameOpenInverse
public import RothschildStein.L1.CanonicalAntisymmetry
public import RothschildStein.L1.CanonicalReversal
public import RothschildStein.L1.SymmetricProductPatch
public import RothschildStein.L1.CanonicalCoefficientPatch
public import RothschildStein.L1.FrameIndependenceNeighborhood
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- Actual canonical chart data retaining its flow, ODE, domains and
inverse identities for subsequent weighted-jet and density arguments. -/
structure CanonicalFrameChartData {N : ℕ}
    (Ω : Set (Fin N → ℝ))
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) where
  initialRadius : ℝ
  initialRadius_pos : 0 < initialRadius
  timeRadius : ℝ
  timeRadius_pos : 0 < timeRadius
  time : ℝ
  time_pos : 0 < time
  time_lt : time < timeRadius
  flow : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ)
  flow_smooth : ContDiffOn ℝ (⊤ : ℕ∞) flow
    (ball (0,x) initialRadius ×ˢ Ioo (-timeRadius) timeRadius)
  flow_ode : ∀ q ∈ ball (0,x) initialRadius, flow (q,0) = q.2 ∧
    ∀ t ∈ Ioo (-timeRadius) timeRadius,
      HasDerivAt (fun s => flow (q,s)) (frameCoefficientField Y (q.1,flow (q,t))) t ∧
      flow (q,t) ∈ Ω
  flow_zero : ∀ y ∈ ball x initialRadius, ∀ t ∈ Ioo (-timeRadius) timeRadius,
    flow ((0,y),t) = y
  inverseDomain : Set ((Fin N → ℝ) × (Fin N → ℝ))
  inverseDomain_open : IsOpen inverseDomain
  theta : ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ)
  theta_smooth : ContDiffOn ℝ (⊤ : ℕ∞) theta inverseDomain
  right_inverse : ∀ q ∈ inverseDomain, canonicalFrameMap time flow (q.1,theta q) = q.2
  inverse_parameters : ∀ q ∈ inverseDomain,
    (time⁻¹ • theta q,q.1) ∈ ball (0,x) initialRadius
  radius : ℝ
  radius_pos : 0 < radius
  radius_le_initial : radius ≤ initialRadius
  closedPatch_subset : closedBall x radius ⊆ Ω
  basePatch_subset : ball x radius ×ˢ ball x radius ⊆ inverseDomain
  antisymmetric : ∀ q ∈ inverseDomain, theta (q.2,q.1) = -theta q
  frame : ∀ y ∈ ball x radius, LinearIndependent ℝ (fun i => Y i y)
  forward_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (canonicalFrameMap time flow)
    (ball x radius ×ˢ ball 0 radius)
  coefficients : ∀ q ∈ ball x radius ×ˢ ball 0 radius,
    (time⁻¹ • q.2,q.1) ∈ ball (0,x) initialRadius ∧
    (q.1,canonicalFrameMap time flow q) ∈ inverseDomain ∧
    theta (q.1,canonicalFrameMap time flow q) = q.2
end RothschildStein.L1
