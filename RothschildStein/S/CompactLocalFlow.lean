-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactFieldGermExtension
public import RothschildStein.S.UniformSmoothBallFlow
public import RothschildStein.S.CompactFlowTube

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology NNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- A smooth field on an open set has one jointly smooth
flow on a neighborhood of any interior compact set, with a common closed
time interval staying inside the original domain. No rank or nonvanishing
assumption is needed (BB Prop 2.22, pp. 88–90). -/
theorem exists_compact_local_smooth_flow
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ))) :
    ∃ σ : ℝ,0 < σ ∧ ∃ W : Set (Fin n → ℝ),IsOpen W ∧
      (K : Set (Fin n → ℝ)) ⊆ W ∧ W ⊆ Ω ∧
      ∃ Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Φ (W ×ˢ Ioo (-σ) σ) ∧
        ∀ x ∈ W,Φ (x,0) = x ∧ ∀ t ∈ Icc (-σ) σ,
          Φ (x,t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t := by
  obtain ⟨B,hB,_,hG⟩ := exists_compact_global_field_germ_extension Ω K hK X hX
  let V := (Ω : Set (Fin n → ℝ)) ∩ interior {x | B x = X x}
  have hVo : IsOpen V := Ω.isOpen.inter isOpen_interior
  have hKV : (K : Set (Fin n → ℝ)) ⊆ V := by
    intro x hx
    exact ⟨hK hx,mem_interior_iff_mem_nhds.mpr (hG x hx)⟩
  have hVe : ∀ x ∈ V,B x = X x := fun x hx => (interior_subset (s := {y | B y = X y}) hx.2)
  obtain ⟨L,hL⟩ := K.isCompact.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : Fin n → ℝ => x) K)
  let a : ℝ≥0 := ⟨2*(|L|+1),by positivity⟩
  have ha : 0 < a := by change 0 < 2*(|L|+1); positivity
  have hKU : (K : Set (Fin n → ℝ)) ⊆ ball 0 (a/2 : ℝ≥0) := by
    intro x hx
    rw [mem_ball,dist_zero_right]
    have hbd : ‖x‖ ≤ |L| := (hL x hx).trans (le_abs_self L)
    change ‖x‖ < 2*(|L|+1)/2
    linarith
  obtain ⟨τ,hτ,Φ,hΦ,hsol⟩ := exists_uniform_smooth_ball_flow B hB 0 a ha
  obtain ⟨σ,hσ,W,hWo,hKW,hWU,hTube⟩ := exists_compact_flow_tube
    (K : Set (Fin n → ℝ)) (ball 0 (a/2 : ℝ≥0)) V K.isCompact isOpen_ball hVo
    hKU hKV τ hτ Φ hΦ.continuousOn (fun x hx => (hsol x (hKU hx)).1)
  have hWΩ : W ⊆ Ω := by
    intro x hx
    have hV := (hTube x hx 0 ⟨by linarith,by linarith⟩).2
    rw [(hsol x (hWU hx)).1] at hV
    exact hV.1
  refine ⟨σ,hσ,W,hWo,hKW,hWΩ,Φ,hΦ.mono ?_,?_⟩
  · rintro ⟨x,t⟩ ⟨hx,ht⟩
    exact ⟨hWU hx,(hTube x hx t (Ioo_subset_Icc_self ht)).1⟩
  · intro x hx
    refine ⟨(hsol x (hWU hx)).1,?_⟩
    intro t ht
    obtain ⟨htτ,hV⟩ := hTube x hx t ht
    refine ⟨hV.1,?_⟩
    simpa only [hVe (Φ (x,t)) hV] using ((hsol x (hWU hx)).2 t htτ).2

end RothschildStein.S
