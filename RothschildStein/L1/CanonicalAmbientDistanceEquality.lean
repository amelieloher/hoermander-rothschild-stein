-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.SmallBallDistanceEquality
public import RothschildStein.L1.CanonicalOrdinaryControlCost
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1

/-- On a common smaller canonical patch, both actual distances
agree with those in every containing ambient domain. Smoothness and rank
are required only on the original free-coordinate domain. -/
theorem exists_canonical_ambient_distance_equalities {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 1 ≤ s)
    (hw : ∀ i, (p i : ℕ) ≤ s)
    {U : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hU : IsOpen U)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U p X s)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData U (canonicalWordFrame D X) x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ C.radius ∧
      ∀ Ω : Set (Fin (freeDimension (k+1) s p) → ℝ), U ⊆ Ω →
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r,
        controlDistance Ω p X η ξ = controlDistance U p X η ξ ∧
        G4.auxiliaryDistance (s := s) Ω p X η ξ = G4.auxiliaryDistance (s := s) U p X η ξ := by
  have hCr := C.radius_pos
  let K := closedBall x (C.radius/2)
  have hKU : K ⊆ U := (closedBall_subset_closedBall (by linarith)).trans C.closedPatch_subset
  obtain ⟨R,hR,he⟩ := exists_compact_controlDistance_domain_equality hU
    (isCompact_closedBall x (C.radius/2)) hKU X hX p
  let Z := fun j : Fin (Fintype.card (G4.ShortWord p s)) =>
    G4.shortField p X (G4.shortIndex p j)
  let w := fun j : Fin (Fintype.card (G4.ShortWord p s)) =>
    G4.shortWeight p (G4.shortIndex p j)
  have hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) U :=
    fun j => G4.shortField_contDiffOn hU hX _
  obtain ⟨RStar,hRStar,heStar⟩ := exists_compact_controlDistance_domain_equality hU
    (isCompact_closedBall x (C.radius/2)) hKU Z hZ w
  obtain ⟨r₁,A,hr₁,hr₁C,hA,hcost⟩ := exists_canonical_ordinary_control_cost D hs hw hU X hX hstep C
  obtain ⟨r₂,hr₂,hr₂C,hsmall⟩ := C.exists_small_gauge_patch D.group
    (lt_min (div_pos hR hA) hRStar)
  let r := min r₁ (min r₂ (C.radius/2))
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ (by positivity))
  refine ⟨r,hr,(min_le_left _ _).trans hr₁C,?_⟩
  intro Ω hUΩ η hη ξ hξ
  have hη₁ := ball_subset_ball (min_le_left r₁ _) hη
  have hξ₁ := ball_subset_ball (min_le_left r₁ _) hξ
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hη₂ := ball_subset_ball hrr₂ hη
  have hξ₂ := ball_subset_ball hrr₂ hξ
  have hηK : η ∈ K := ball_subset_closedBall
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hη)
  have hg := hsmall η hη₂ ξ hξ₂
  have hρR : A*rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) < R := by
    have hh := (lt_div_iff₀ hA).mp (hg.trans_le (min_le_left _ _))
    simpa only [mul_comm] using hh
  have hρStar : rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) < RStar :=
    hg.trans_le (min_le_right _ _)
  constructor
  · exact he Ω hUΩ η hηK ξ ((hcost η hη₁ ξ hξ₁).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hρR))
  · exact heStar Ω hUΩ η hηK ξ ((auxiliaryDistance_le_canonical_gauge D X C
      (ball_subset_ball hr₂C hη₂) (ball_subset_ball hr₂C hξ₂)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hRStar).mpr hρStar))
end RothschildStein.L1
