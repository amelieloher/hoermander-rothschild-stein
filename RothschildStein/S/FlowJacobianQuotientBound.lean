-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FlowJacobianContinuity
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.S
variable {n : ℕ}

/-- Joint continuity and the scalar mean value theorem give a uniform bound for inverse-Jacobian difference quotients on a compact set of starting points and a closed time interval (BB (2.29)–(2.30), p. 90). -/
theorem exists_uniform_inverse_jacobian_quotient_bound
    {Ω U K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ δ : ℝ}
    (hδ : 0 < δ) (hδτ : δ < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ x ∈ K,∀ t ∈ Icc (-δ) δ,t ≠ 0 →
      |((fderiv ℝ (fun y => Φ (y,-t)) x).det-1)/t| ≤ M := by
  let D := U ×ˢ Ioo (-τ) τ
  let F := fun p : ((Fin n → ℝ) × ℝ) =>
    Hormander.Interface.euclideanDivergence X (Φ p) *
      (fderiv ℝ (fun y => Φ (y,p.2)) p.1).det
  have hc : ContinuousOn F D :=
    ((continuousOn_smooth_field_divergence hΩ X hX).comp hjoint.continuousOn
      (fun p hp => ((hΦ p.1 hp.1).2 p.2 hp.2).2)).mul
      (continuousOn_flow_jacobian hU Φ hjoint)
  have htime : Icc (-δ) δ ⊆ Ioo (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨M,hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono hKU htime))
  refine ⟨max M 0,le_max_right M 0,?_⟩
  intro x hx t ht ht0
  have hneg : -t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1,ht.2]
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith,by linarith⟩
  have hsub : uIcc 0 (-t) ⊆ Icc (-δ) δ := ordConnected_Icc.uIcc_subset hzero hneg
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (flow_jacobian_hasDerivAt hΩ hU hX Φ hjoint
      (fun y hy => (hΦ y hy).2) (hKU hx) (htime (hsub hs))).hasDerivWithinAt)
    (fun s hs => (hM (x,s) ⟨hx,hsub hs⟩).trans (le_max_left M 0))
    (convex_uIcc 0 (-t)) (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 (-t))
    (right_mem_uIcc : -t ∈ uIcc 0 (-t))
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr ht0)).mpr
  simpa only [Real.norm_eq_abs,sub_zero,abs_neg,
    flow_jacobian_eq_one_at_zero hU Φ (fun y hy => (hΦ y hy).1) (hKU hx)] using H

end RothschildStein.S
