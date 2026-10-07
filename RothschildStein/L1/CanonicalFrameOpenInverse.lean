-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameSmoothness
public import RothschildStein.L1.OpenParameterInverse
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

/-- The inverse of an actual frame flow is jointly smooth on a
common open neighborhood of the diagonal. -/
theorem canonicalFrameMap_open_inverse_of_flow {N : ℕ}
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
          (∀ᶠ q in 𝓝 (x,0), Θ (q.1,canonicalFrameMap a Φ q) = q.2) := by
  have hd := canonicalFrameMap_hasFDerivAt ha Φ x (frameValueCLM Y x)
    (frameFlow_hasFDerivAt_of_flow hΩ hU hτ Y hY Φ hΦ hinit hsol x hx hfix hat)
  have hde : HasFDerivAt (canonicalFrameMap a Φ)
      ((ContinuousLinearMap.id ℝ _).coprod (frameValueEquiv Y x hframe : _ →L[ℝ] _)) (x,0) := by
    convert hd using 1
    apply congrArg ((ContinuousLinearMap.id ℝ _).coprod)
    apply ContinuousLinearMap.ext
    intro u
    exact frameValueEquiv_apply Y x hframe u
  have hp : (x,0) ∈ canonicalFrameDomain a U := by
    simpa [canonicalFrameDomain] using hx
  have hkx : canonicalFrameMap a Φ (x,0) = x := by
    simpa [canonicalFrameMap] using hfix a hat
  obtain ⟨W,hW,hpW,Θ,hΘ,hΘx,hright,hleft⟩ := exists_open_parameter_inverse
    (canonicalFrameMap a Φ) (canonicalFrameDomain_isOpen a hU)
    (canonicalFrameMap_contDiffOn a hat Φ hΦ) (x,0) hp
    (ContinuousLinearMap.id ℝ _) (frameValueEquiv Y x hframe) hde
  refine ⟨W,hW,?_,Θ,hΘ,?_,hright,hleft⟩
  · simpa only [hkx] using hpW
  · simpa only [hkx] using hΘx
end RothschildStein.L1
