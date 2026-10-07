-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.QuantitativeExistence
public import RothschildStein.G1.SmoothDependenceMain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- A global smooth field has one jointly smooth flow
for every starting point in a prescribed half-radius ball. The time
interval is uniform and the curves stay in the full-radius closed ball.
G1 supplies Picard existence and joint regularity
(BB Prop 2.22, pp. 88–90; compact-support flow reduction). -/
theorem exists_uniform_smooth_ball_flow
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (x₀ : Fin n → ℝ) (a : ℝ≥0) (ha : 0 < a) :
    ∃ τ : ℝ,0 < τ ∧ ∃ Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ (ball x₀ (a/2 : ℝ≥0) ×ˢ Ioo (-τ) τ) ∧
      ∀ x ∈ ball x₀ (a/2 : ℝ≥0),Φ (x,0) = x ∧
      ∀ t ∈ Ioo (-τ) τ,Φ (x,t) ∈ closedBall x₀ a ∧
        HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t := by
  obtain ⟨L,hL⟩ := (isCompact_closedBall x₀ (a : ℝ)).exists_bound_of_continuousOn
    hX.continuous.continuousOn
  have hL0 : 0 ≤ L := (norm_nonneg (X x₀)).trans
    (hL x₀ (mem_closedBall_self a.2))
  let LN : ℝ≥0 := ⟨L,hL0⟩
  have hlocal : LocallyLipschitzOn (closedBall x₀ (a : ℝ)) X := by
    intro x _
    obtain ⟨K,s,hs,hK⟩ := (hX.of_le (by simp)).contDiffAt.exists_lipschitzOnWith
    exact ⟨K,s,mem_nhdsWithin_of_mem_nhds hs,hK⟩
  obtain ⟨K,hK⟩ := hlocal.exists_lipschitzOnWith_of_compact (isCompact_closedBall x₀ (a : ℝ))
  obtain ⟨Φ,hct,hΦ⟩ := G1.exists_flow_with_explicit_time ha
    (Z := X) (L := LN) (fun x hx => hL x hx) hK
  let τ : ℝ := a/(4*(LN+1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hc : ContinuousOn Φ (ball x₀ (a/2 : ℝ≥0) ×ˢ Ioo (-τ) τ) :=
    hct.mono (Set.prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
  have hi : ∀ x ∈ ball x₀ (a/2 : ℝ≥0),Φ (x,0) = x :=
    fun x hx => (hΦ x (ball_subset_closedBall hx)).1
  have hsol : ∀ x ∈ ball x₀ (a/2 : ℝ≥0),∀ t ∈ Ioo (-τ) τ,
      Φ (x,t) ∈ Set.univ ∧ HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t :=
    fun x hx t ht => ⟨mem_univ _,((hΦ x (ball_subset_closedBall hx)).2 t ht).2⟩
  refine ⟨τ,hτ,Φ,?_,fun x hx => ⟨hi x hx,fun t ht =>
    (hΦ x (ball_subset_closedBall hx)).2 t ht⟩⟩
  exact G1.local_flow_contDiffOn isOpen_univ isOpen_ball hτ hX.contDiffOn hc hi hsol

end RothschildStein.S
