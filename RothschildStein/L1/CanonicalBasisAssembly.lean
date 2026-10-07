-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalBasisValues
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

/-- The coefficient derivative of the actual canonical map at
zero is exactly the chosen tangent frame. -/
theorem canonicalFrameMap_coefficients_hasFDerivAt_of_flow {N : ℕ}
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
    (η : Fin N → ℝ) (hη : (0,η) ∈ U)
    (hfix : ∀ t ∈ Ioo (-τ) τ, Φ ((0,η),t) = η) :
    HasFDerivAt (fun u => canonicalFrameMap a Φ (η,u)) (frameValueCLM Y η) 0 := by
  have hd := canonicalFrameMap_hasFDerivAt ha Φ η (frameValueCLM Y η)
    (frameFlow_hasFDerivAt_of_flow hΩ hU hτ Y hY Φ hΦ hinit hsol η hη hfix hat)
  have hh := hd.comp (0 : Fin N → ℝ)
    ((hasFDerivAt_const η (0 : Fin N → ℝ)).prodMk (hasFDerivAt_id (0 : Fin N → ℝ)))
  have he : ((ContinuousLinearMap.id ℝ _).coprod (frameValueCLM Y η)).comp
      ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ _)) =
      frameValueCLM Y η := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [he] at hh
  exact hh
end RothschildStein.L1
