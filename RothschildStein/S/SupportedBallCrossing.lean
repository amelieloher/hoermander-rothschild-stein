-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ControlCurveCertificates
public import RothschildStein.S.DistanceMetricLaws
public import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- A near-minimizing controlled curve from the compact support to outside a ball contains an interior point in the ball but outside the support (BB Proposition 2.18(iii), p. 85). -/
theorem exists_interior_zero_support_crossing
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hG : G.d = controlDistance (Ω : Set (Fin n → ℝ)) w X)
    (hw : ∀ i,(w i : ℕ) ≤ 2) (x₀ : Ω) {R : ℝ≥0∞}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKB : ∀ z ∈ K,z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R)
    {x y : Fin n → ℝ} (hx : x ∈ K) (_hy : y ∈ (Ω : Set (Fin n → ℝ)))
    (hyB : ¬ G.d x₀.val y < R) {δ : ℝ}
    (hd : G.d x y < ENNReal.ofReal δ) :
    ∃ z : Fin n → ℝ,z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d x₀.val z < R ∧
      z ∉ K ∧ G.d x z ≤ ENNReal.ofReal δ := by
  obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn ⟨x,hx⟩
    ((G.continuousOn_distance x₀).mono (fun a ha => (hKB a ha).1))
  obtain ⟨r,hr1,hr2⟩ := exists_between (hKB z hz).2
  obtain ⟨γ,hγ,h0,h1,hcts,hbound⟩ := exists_controlled_curve_distance_certificate hw (hG ▸ hd)
  have hct : ContinuousOn (fun t => G.d x₀.val (γ t)) (Icc (0 : ℝ) 1) :=
    (G.continuousOn_distance x₀).comp hcts hγ.2.2.1
  have hleft : G.d x₀.val (γ 0) ≤ r := by rw [h0]; exact (hm hx).trans hr1.le
  have hright : r ≤ G.d x₀.val (γ 1) := by rw [h1]; exact hr2.le.trans (le_of_not_gt hyB)
  obtain ⟨t,ht,hrt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hct ⟨hleft,hright⟩
  dsimp only at hrt
  refine ⟨γ t,hγ.2.2.1 ht,by rw [hrt]; exact hr2,?_,?_⟩
  · intro htk
    have h : G.d x₀.val (γ t) ≤ G.d x₀.val z := hm htk
    rw [hrt] at h
    exact (not_le_of_gt hr1) h
  · have hb := hbound 0 (by norm_num) t ht
    rw [h0,← hG] at hb
    have hδ : 0 ≤ δ := hγ.1.le
    have hs : Real.sqrt |0-t| ≤ 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by norm_num,by simpa only [zero_sub,abs_neg,abs_of_nonneg ht.1,one_pow] using ht.2⟩
    exact hb.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

end RothschildStein.S
