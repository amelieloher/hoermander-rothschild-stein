-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactLocalFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The compact local flow has a smaller neighborhood
whose trajectories remain in its initial-point domain. A single interior
compact set contains every forward and backward trajectory from K.
This supplies the buffer for the inverse maps and the common integration
support in BB Prop 2.22, pp. 88–90. -/
theorem exists_compact_local_flow_buffer
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ))) :
    ∃ τ : ℝ,0 < τ ∧ ∃ U V : Set (Fin n → ℝ),IsOpen U ∧ IsOpen V ∧
      (K : Set (Fin n → ℝ)) ⊆ V ∧ V ⊆ U ∧ U ⊆ Ω ∧
      ∃ Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ) ∧
        (∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
          Φ (x,t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t) ∧
        ∃ δ : ℝ,0 < δ ∧ δ < τ ∧
          (∀ x ∈ V,∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ U) ∧
          ∃ C : Compacts (Fin n → ℝ),(C : Set (Fin n → ℝ)) ⊆ Ω ∧
            (K : Set (Fin n → ℝ)) ⊆ C ∧
            ∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ C := by
  obtain ⟨τ,hτ,U,hU,hKU,hUΩ,Φ,hΦ,hsol⟩ := exists_compact_local_smooth_flow Ω K hK X hX
  obtain ⟨σ,hσ,V,hV,hKV,hVU,hTube⟩ := exists_compact_flow_tube
    (K : Set (Fin n → ℝ)) U U K.isCompact hU hU hKU hKU τ hτ Φ
    hΦ.continuousOn (fun x hx => (hsol x (hKU hx)).1)
  let δ : ℝ := min σ (τ/2)
  have hδ : 0 < δ := lt_min hσ (by linarith)
  have hδτ : δ < τ := (min_le_right σ (τ/2)).trans_lt (by linarith)
  have hδσ : δ ≤ σ := min_le_left σ (τ/2)
  have htime : Icc (-δ) δ ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have htimeσ : Icc (-δ) δ ⊆ Icc (-σ) σ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hct : ContinuousOn Φ ((K : Set (Fin n → ℝ)) ×ˢ Icc (-δ) δ) :=
    hΦ.continuousOn.mono (Set.prod_mono hKU htime)
  let C : Compacts (Fin n → ℝ) := ⟨Φ '' ((K : Set (Fin n → ℝ)) ×ˢ Icc (-δ) δ),
    (K.isCompact.prod isCompact_Icc).image_of_continuousOn hct⟩
  refine ⟨τ,hτ,U,V,hU,hV,hKV,hVU,hUΩ,Φ,hΦ,?_,δ,hδ,hδτ,?_,C,?_,?_,?_⟩
  · intro x hx
    exact ⟨(hsol x hx).1,fun t ht => (hsol x hx).2 t (Ioo_subset_Icc_self ht)⟩
  · intro x hx t ht
    exact (hTube x hx t (htimeσ ht)).2
  · rintro y ⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩
    exact ((hsol x (hKU hx)).2 t (Ioo_subset_Icc_self (htime ht))).1
  · intro x hx
    exact ⟨(x,0),⟨hx,by constructor <;> linarith⟩,(hsol x (hKU hx)).1⟩
  · intro x hx t ht
    exact ⟨(x,t),⟨hx,ht⟩,rfl⟩

end RothschildStein.S
