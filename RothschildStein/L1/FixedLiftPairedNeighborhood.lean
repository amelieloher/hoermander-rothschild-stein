-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FixedLiftPairedFamilies
public import RothschildStein.L1.PairedFamilyCenterNeighborhood
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- At each point of the fixed free patch, both actual joint
families and a common closed center neighborhood exist. No independent
chart, flow or coefficient-domain existence premise is required. -/
theorem FixedLiftData.exists_pairedJointShortChartNeighborhood {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)}
    {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (L : FixedLiftData w s Ω X x₀ m) (hn : 0 < n) (hs : 0 < s)
    (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {tO tl : ℝ} (htO : 0 < tO) (htO1 : tO < 1) (htl : 0 < tl) (htl1 : tl < 1)
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ L.U) :
    ∃ Fo : JointShortChartFamily (n := n) (s := s) w
        (basePoint '' (L.U : Set (Fin (n+m) → ℝ))) X (basePoint ξ) tO,
    ∃ Fl : JointShortChartFamily (n := n+m) (s := s) w
        (L.U : Set (Fin (n+m) → ℝ)) (triangularLift X L.P) ξ tl,
    ∃ R : ℝ, 0 < R ∧ ∀ ζ ∈ closedBall ξ R,
      basePoint ζ ∈ closedBall (basePoint ξ) (Fo.R/16) ∧
      ζ ∈ closedBall ξ (Fl.R/16) := by
  obtain ⟨⟨Fo⟩,⟨Fl⟩⟩ := L.nonempty_pairedJointShortChartFamilies
    hn hs hΩ hX htO htO1 htl htl1 hξ
  obtain ⟨R,hR,hcenters⟩ := paired_family_center_neighborhood Fo Fl
  exact ⟨Fo,Fl,R,hR,hcenters⟩

end RothschildStein.L1
