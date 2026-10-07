-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameOpenInverse
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

/-- Shrinking the inverse neighborhood also places every inverse
coefficient pair in the actual forward-flow domain. -/
theorem canonicalFrameMap_open_inverse_with_domain_of_flow {N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {τ a : ℝ} (hτ : 0 < τ)
    (ha : a ≠ 0) (hat : a ∈ Ioo (-τ) τ)
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hinit : ∀ q ∈ U, Φ (q,0) = q.2)
    (hsol : ∀ q ∈ U, ∀ t ∈ Ioo (-τ) τ, Φ (q,t) ∈ Ω ∧
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t)
    (x : Fin N → ℝ) (hx : (0,x) ∈ U)
    (hfix : ∀ t ∈ Ioo (-τ) τ, Φ ((0,x),t) = x)
    (hframe : LinearIndependent ℝ (fun i => Y i x)) :
    ∃ W : Set ((Fin N → ℝ) × (Fin N → ℝ)), IsOpen W ∧ (x,x) ∈ W ∧
      ∃ Θ : ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Θ W ∧ Θ (x,x) = 0 ∧
        (∀ q ∈ W, canonicalFrameMap a Φ (q.1,Θ q) = q.2) ∧
        (∀ q ∈ W, (a⁻¹ • Θ q,q.1) ∈ U) ∧
        (∀ᶠ q in 𝓝 (x,0), Θ (q.1,canonicalFrameMap a Φ q) = q.2) := by
  obtain ⟨W,hW,hpW,Θ,hΘ,hΘx,hright,hleft⟩ := canonicalFrameMap_open_inverse_of_flow
    hΩ hU hτ ha hat Y hY Φ hΦ hinit hsol x hx hfix hframe
  have hc : ContinuousAt (fun q => (a⁻¹ • Θ q,q.1)) (x,x) :=
    (((hΘ.contDiffAt (hW.mem_nhds hpW)).continuousAt).const_smul a⁻¹).prodMk continuousAt_fst
  have hm : {q | (a⁻¹ • Θ q,q.1) ∈ U} ∈ 𝓝 (x,x) :=
    hc.preimage_mem_nhds (by simpa only [hΘx,smul_zero] using hU.mem_nhds hx)
  obtain ⟨V,hVsub,hVopen,hpV⟩ := mem_nhds_iff.mp hm
  refine ⟨W ∩ V,hW.inter hVopen,⟨hpW,hpV⟩,Θ,hΘ.mono inter_subset_left,hΘx,
    fun q hq => hright q hq.1,fun q hq => hVsub hq.2,hleft⟩
end RothschildStein.L1
