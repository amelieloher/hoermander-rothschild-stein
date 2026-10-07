-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameSmoothness
public import RothschildStein.L1.FrameFlowReversal
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

/-- On a neighborhood of the zero-coefficient point, the actual
canonical trajectories reverse. Openness supplies every endpoint-domain
condition needed by actual flow uniqueness. -/
theorem canonicalFrameMap_reverse_eventually {N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {τ a : ℝ} (hτ : 0 < τ)
    (hat : a ∈ Ioo (-τ) τ)
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hsol : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧
      Φ (q,t) ∈ Ω)
    (x : Fin N → ℝ) (hx : (0,x) ∈ U)
    (hfix : Φ ((0,x),a) = x) :
    ∀ᶠ q in 𝓝 (x,0), canonicalFrameMap a Φ (canonicalFrameMap a Φ q,-q.2) = q.1 := by
  let K := canonicalFrameMap a Φ
  have hp : (x,0) ∈ canonicalFrameDomain a U := by
    simpa [canonicalFrameDomain] using hx
  have hk : K (x,0) = x := by simpa [K,canonicalFrameMap] using hfix
  have hc : ContinuousAt K (x,0) :=
    ((canonicalFrameMap_contDiffOn a hat Φ hΦ).contDiffAt
      ((canonicalFrameDomain_isOpen a hU).mem_nhds hp)).continuousAt
  have hT : ContinuousAt (fun q : (Fin N → ℝ) × (Fin N → ℝ) => (a⁻¹ • q.2,q.1)) (x,0) :=
    (continuousAt_snd.const_smul a⁻¹).prodMk continuousAt_fst
  have hS : ContinuousAt (fun q : (Fin N → ℝ) × (Fin N → ℝ) => (a⁻¹ • q.2,K q)) (x,0) :=
    (continuousAt_snd.const_smul a⁻¹).prodMk hc
  have hR : ContinuousAt (fun q : (Fin N → ℝ) × (Fin N → ℝ) => (-(a⁻¹ • q.2),K q)) (x,0) :=
    (continuousAt_snd.const_smul a⁻¹).neg.prodMk hc
  have ht : ∀ᶠ q in 𝓝 (x,0), (a⁻¹ • q.2,q.1) ∈ U :=
    hT.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  have hs : ∀ᶠ q in 𝓝 (x,0), (a⁻¹ • q.2,K q) ∈ U :=
    hS.preimage_mem_nhds (by simpa only [smul_zero,hk] using hU.mem_nhds hx)
  have hr : ∀ᶠ q in 𝓝 (x,0), (-(a⁻¹ • q.2),K q) ∈ U :=
    hR.preimage_mem_nhds (by simpa only [smul_zero,neg_zero,hk] using hU.mem_nhds hx)
  filter_upwards [ht,hs,hr] with q hq he hne
  simpa only [K,canonicalFrameMap,smul_neg] using
    frameFlow_reverse_endpoint hΩ hτ Y hY Φ hsol (a⁻¹ • q.2) q.1 hq hat he hne
end RothschildStein.L1
