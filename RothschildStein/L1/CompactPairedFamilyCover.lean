-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FixedLiftPairedNeighborhood
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- Compact sets have a finite cover by compatible actual
original/lifted joint families. The families and center neighborhoods
are fixed before any application scale or frame is chosen; empty compact
sets require no exceptional geometric hypothesis. -/
theorem FixedLiftData.exists_compact_pairedJointShortChartCover {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)}
    {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (L : FixedLiftData w s Ω X x₀ m) (hn : 0 < n) (hs : 0 < s)
    (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {tO tl : ℝ} (htO : 0 < tO) (htO1 : tO < 1) (htl : 0 < tl) (htl1 : tl < 1)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ L.U) :
    ∃ Fo : ∀ ξ : K, JointShortChartFamily (n := n) (s := s) w
        (basePoint '' (L.U : Set (Fin (n+m) → ℝ))) X (basePoint ξ.val) tO,
    ∃ Fl : ∀ ξ : K, JointShortChartFamily (n := n+m) (s := s) w
        (L.U : Set (Fin (n+m) → ℝ)) (triangularLift X L.P) ξ.val tl,
    ∃ R : K → ℝ, ∃ S : Finset K,
      (∀ ξ : K, 0 < R ξ ∧ ∀ ζ ∈ closedBall ξ.val (R ξ),
        basePoint ζ ∈ closedBall (basePoint ξ.val) ((Fo ξ).R/16) ∧
        ζ ∈ closedBall ξ.val ((Fl ξ).R/16)) ∧
      K ⊆ ⋃ ξ ∈ S, ball ξ.val (R ξ) := by
  classical
  have hlocal : ∀ ξ : K,
      ∃ Fo : JointShortChartFamily (n := n) (s := s) w
          (basePoint '' (L.U : Set (Fin (n+m) → ℝ))) X (basePoint ξ.val) tO,
      ∃ Fl : JointShortChartFamily (n := n+m) (s := s) w
          (L.U : Set (Fin (n+m) → ℝ)) (triangularLift X L.P) ξ.val tl,
      ∃ R : ℝ, 0 < R ∧ ∀ ζ ∈ closedBall ξ.val R,
        basePoint ζ ∈ closedBall (basePoint ξ.val) (Fo.R/16) ∧
        ζ ∈ closedBall ξ.val (Fl.R/16) := fun ξ =>
    L.exists_pairedJointShortChartNeighborhood hn hs hΩ hX htO htO1 htl htl1 (hKU ξ.property)
  choose Fo Fl R hR hcenter using hlocal
  have hcover : K ⊆ ⋃ ξ : K, ball ξ.val (R ξ) := by
    intro ζ hζ
    exact mem_iUnion.mpr ⟨⟨ζ,hζ⟩,mem_ball_self (hR ⟨ζ,hζ⟩)⟩
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover (fun ξ : K => ball ξ.val (R ξ))
    (fun _ => isOpen_ball) hcover
  exact ⟨Fo,Fl,R,S,fun ξ => ⟨hR ξ,hcenter ξ⟩,hS⟩

end RothschildStein.L1
