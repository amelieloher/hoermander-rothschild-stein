-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowComposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.S
variable {n : ℕ}

/-- A flow time map is injective on any starting set
whose trajectories stay in the initial-point domain (BB p. 89). -/
theorem flow_time_injOn
    {Ω U V : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hVU : V ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hstay : ∀ x ∈ V,Φ (x,t) ∈ U) : InjOn (fun x => Φ (x,t)) V := by
  intro x hx y hy he
  have hxinv := G1.localFlow_inverse hΩ hX hτ Φ hΦ (hVU hx) ht (hstay x hx)
  have hyinv := G1.localFlow_inverse hΩ hX hτ Φ hΦ (hVU hy) ht (hstay y hy)
  change Φ (x,t) = Φ (y,t) at he
  rw [he] at hxinv
  exact hxinv.symm.trans hyinv

/-- The image of a buffered start set is the relative
preimage under the opposite-time map. This also identifies its inverse
without a global flow assumption (BB p. 89). -/
theorem flow_image_eq_inter_preimage
    {Ω U V : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hVU : V ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hstay : ∀ x ∈ V,Φ (x,t) ∈ U) :
    (fun x => Φ (x,t)) '' V = U ∩ (fun y => Φ (y,-t)) ⁻¹' V := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hstay x hx,by
      change Φ (Φ (x,t),-t) ∈ V
      rw [G1.localFlow_inverse hΩ hX hτ Φ hΦ (hVU hx) ht (hstay x hx)]
      exact hx⟩
  · intro hy
    have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    refine ⟨Φ (y,-t),hy.2,?_⟩
    simpa only [neg_neg] using G1.localFlow_inverse hΩ hX hτ Φ hΦ hy.1 hneg (hVU hy.2)

/-- The buffered flow image is open: its inverse-time
preimage description and joint continuity suffice (BB p. 89). -/
theorem isOpen_flow_image
    {Ω U V : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hstay : ∀ x ∈ V,Φ (x,t) ∈ U) : IsOpen ((fun x => Φ (x,t)) '' V) := by
  rw [flow_image_eq_inter_preimage hΩ hVU hX hτ Φ hΦ ht hstay]
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hc' : ContinuousOn (fun y => Φ (y,-t)) U :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy,hneg⟩)
  exact hc'.isOpen_inter_preimage hU hV

end RothschildStein.S
