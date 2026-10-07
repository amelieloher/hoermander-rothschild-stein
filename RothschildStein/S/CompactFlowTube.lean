-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.S
variable {E : Type*} [MetricSpace E]

/-- A continuous flow fixing time zero stays in a prescribed
open set for a common closed time interval and an open neighborhood of
any compact set of starting points (BB Prop 2.22, pp. 88–90).
The compact tube gives the support buffer used in dominated convergence. -/
theorem exists_compact_flow_tube
    (K U V : Set E) (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
    (hKU : K ⊆ U) (hKV : K ⊆ V) (τ : ℝ) (hτ : 0 < τ)
    (Φ : E × ℝ → E) (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hi : ∀ x ∈ K,Φ (x,0) = x) :
    ∃ σ : ℝ,0 < σ ∧ ∃ W : Set E,IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧
      ∀ x ∈ W,∀ t ∈ Icc (-σ) σ,t ∈ Ioo (-τ) τ ∧ Φ (x,t) ∈ V := by
  let O := (U ×ˢ Ioo (-τ) τ) ∩ Φ ⁻¹' V
  have hO : IsOpen O := hc.isOpen_inter_preimage (hU.prod isOpen_Ioo) hV
  have hKO : K ×ˢ ({0} : Set ℝ) ⊆ O := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact ⟨⟨hKU hx,by constructor <;> linarith⟩,by simpa [hi x hx] using hKV hx⟩
  obtain ⟨δ,hδ,hδO⟩ := (hK.prod isCompact_singleton).exists_thickening_subset_open hO hKO
  let σ : ℝ := δ/2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσδ : σ < δ := by dsimp [σ]; linarith
  have htube : ∀ x ∈ thickening σ K,∀ t ∈ Icc (-σ) σ,(x,t) ∈ O := by
    intro x hx t ht
    obtain ⟨y,hy,hxy⟩ := mem_thickening_iff.mp hx
    apply hδO
    apply mem_thickening_iff.mpr
    refine ⟨(y,0),⟨hy,mem_singleton 0⟩,?_⟩
    rw [Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff]
    exact ⟨hxy.trans hσδ,(abs_le.mpr ht).trans_lt hσδ⟩
  refine ⟨σ,hσ,thickening σ K,isOpen_thickening,self_subset_thickening hσ K,?_,?_⟩
  · intro x hx
    exact (htube x hx 0 ⟨by linarith,by linarith⟩).1.1
  · intro x hx t ht
    exact ⟨(htube x hx t ht).1.2,(htube x hx t ht).2⟩

end RothschildStein.S
