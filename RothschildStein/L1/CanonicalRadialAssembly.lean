-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalRadialIdentity
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- Actual frame-flow coordinates satisfy the Euler identity at
every point of their common coefficient patch. -/
theorem canonicalPullback_radial_identity_of_flow {N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U W C : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hW : IsOpen W) (hC : IsOpen C)
    {τ a : ℝ} (ha : 0 < a) (haτ : a < τ)
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hsol : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧ Φ (q,t) ∈ Ω)
    (Θ : ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ))
    (hΘ : ContDiffOn ℝ (⊤ : ℕ∞) Θ W)
    (hleft : ∀ q ∈ C, Θ (q.1,canonicalFrameMap a Φ q) = q.2)
    (η u : Fin N → ℝ) (hq : (η,u) ∈ C)
    (hparam : (a⁻¹ • u,η) ∈ U) (htarget : (η,canonicalFrameMap a Φ (η,u)) ∈ W) :
    ∑ i, u i • coordinatePullbackField Y (fun ξ => Θ (η,ξ))
      (fun v => canonicalFrameMap a Φ (η,v)) i u = u := by
  have hθ : DifferentiableAt ℝ (fun ξ => Θ (η,ξ)) (canonicalFrameMap a Φ (η,u)) :=
    ((hΘ.contDiffAt (hW.mem_nhds htarget)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hinv : (fun s : ℝ => Θ (η,canonicalFrameMap a Φ (η,s • u))) =ᶠ[𝓝 1]
      (fun s => s • u) := by
    have hc : ContinuousAt (fun s : ℝ => (η,s • u)) 1 :=
      continuousAt_const.prodMk (continuousAt_id.smul continuousAt_const)
    have hmem : ∀ᶠ s : ℝ in 𝓝 1, (η,s • u) ∈ C :=
      hc.preimage_mem_nhds (by simpa only [one_smul] using hC.mem_nhds hq)
    exact hmem.mono (fun s hs => hleft (η,s • u) hs)
  exact coordinatePullbackField_radial_identity Y (fun ξ => Θ (η,ξ))
    (fun v => canonicalFrameMap a Φ (η,v)) u hθ
    (canonicalFrameMap_radial_hasDerivAt hΩ hU ha haτ Y hY Φ hsol η u hparam) hinv
end RothschildStein.L1
