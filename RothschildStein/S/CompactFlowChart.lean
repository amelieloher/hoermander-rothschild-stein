-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactLocalFlowBuffer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n : ℕ}

/-- Shrinking the common time makes trajectories
from the test support stay in the smaller start set, while trajectories
from that set stay in the larger flow domain. Both time orientations
share an interior compact buffer (BB Prop 2.22, p. 89). -/
theorem exists_compact_flow_chart
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
          (∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ V) ∧
          ∃ C : Compacts (Fin n → ℝ),(C : Set (Fin n → ℝ)) ⊆ Ω ∧
            (K : Set (Fin n → ℝ)) ⊆ C ∧
            ∀ x ∈ (K : Set (Fin n → ℝ)),∀ t ∈ Icc (-δ) δ,Φ (x,t) ∈ C := by
  obtain ⟨τ,hτ,U,V,hU,hV,hKV,hVU,hUΩ,Φ,hΦ,hsol,δ,hδ,hδτ,hstay,C,hCΩ,hKC,hC⟩ :=
    exists_compact_local_flow_buffer Ω K hK X hX
  obtain ⟨σ,hσ,W,_,hKW,_,hTube⟩ := exists_compact_flow_tube
    (K : Set (Fin n → ℝ)) U V K.isCompact hU hV (hKV.trans hVU) hKV τ hτ Φ
    hΦ.continuousOn (fun x hx => (hsol x (hVU (hKV hx))).1)
  let ε : ℝ := min δ σ
  have hε : 0 < ε := lt_min hδ hσ
  have hεδ : ε ≤ δ := min_le_left δ σ
  have hεσ : ε ≤ σ := min_le_right δ σ
  have hsubδ : Icc (-ε) ε ⊆ Icc (-δ) δ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hsubσ : Icc (-ε) ε ⊆ Icc (-σ) σ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨τ,hτ,U,V,hU,hV,hKV,hVU,hUΩ,Φ,hΦ,hsol,ε,hε,hεδ.trans_lt hδτ,
    fun x hx t ht => hstay x hx t (hsubδ ht),?_,C,hCΩ,hKC,
    fun x hx t ht => hC x hx t (hsubδ ht)⟩
  intro x hx t ht
  exact (hTube x (hKW hx) t (hsubσ ht)).2

end RothschildStein.S
