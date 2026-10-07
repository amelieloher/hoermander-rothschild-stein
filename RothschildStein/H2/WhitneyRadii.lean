-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Patches
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- The capped distance-to-boundary radius for Whitney balls. -/
def whitneyRadius (A : Set X) (κ : ℝ) (x : X) : ℝ :=
  min (infDist x Aᶜ / 2) (κ / 5)

/-- Whitney radii are positive and bounded by the prescribed cap
(BB Lemma 7.33, pp. 321–322; radius cap κ/5). -/
theorem whitneyRadius_pos_le {A : Set X} (hA : IsOpen A) (hne : Aᶜ.Nonempty)
    {κ : ℝ} (hκ : 0 < κ) {x : X} (hx : x ∈ A) :
    0 < whitneyRadius A κ x ∧ whitneyRadius A κ x ≤ κ / 5 := by
  have hd : 0 < infDist x Aᶜ := hA.isClosed_compl.notMem_iff_infDist_pos hne |>.mp
    (by simpa using hx)
  exact ⟨lt_min (by positivity) (by positivity), min_le_right _ _⟩

/-- Each proposed Whitney ball lies inside the open set. -/
theorem whitney_ball_subset {A : Set X} (hA : IsOpen A) (hne : Aᶜ.Nonempty)
    {κ : ℝ} (_hκ : 0 < κ) {x : X} (hx : x ∈ A) :
    ball x (whitneyRadius A κ x) ⊆ A := by
  have hd : 0 < infDist x Aᶜ := hA.isClosed_compl.notMem_iff_infDist_pos hne |>.mp
    (by simpa using hx)
  intro y hy
  have hxy : dist x y < infDist x Aᶜ := by
    have hb : dist x y < whitneyRadius A κ x := by simpa [mem_ball, dist_comm] using hy
    have hr : whitneyRadius A κ x ≤ infDist x Aᶜ / 2 := min_le_left _ _
    linarith
  simpa only [mem_compl_iff, not_not] using notMem_of_dist_lt_infDist hxy

/-- An uncapped Whitney ball has a stopping point outside the
open set within four radii; attainment of the infimum is unnecessary. -/
theorem whitney_stopping_point {A : Set X} (hA : IsOpen A) (hne : Aᶜ.Nonempty)
    {κ : ℝ} (hκ : 0 < κ) {x : X} (hx : x ∈ A) :
    whitneyRadius A κ x = κ / 5 ∨
      ∃ y ∉ A, dist x y < 4 * whitneyRadius A κ x := by
  by_cases hc : κ / 5 ≤ infDist x Aᶜ / 2
  · exact Or.inl (min_eq_right hc)
  · right
    have hr : whitneyRadius A κ x = infDist x Aᶜ / 2 :=
      min_eq_left (le_of_not_ge hc)
    have hp := (whitneyRadius_pos_le hA hne hκ hx).1
    obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).mp
      (show infDist x Aᶜ < 4 * whitneyRadius A κ x by rw [hr] at hp ⊢; linarith)
    exact ⟨y, hy, hxy⟩

/-- The boundary distance at a point of an uncapped ball is
between one and three radii, the comparability used for the overlap bound. -/
theorem whitney_boundary_comparable {A : Set X} {κ : ℝ} {x y : X}
    (hr : whitneyRadius A κ x = infDist x Aᶜ / 2)
    (hy : y ∈ ball x (whitneyRadius A κ x)) :
    whitneyRadius A κ x < infDist y Aᶜ ∧
      infDist y Aᶜ < 3 * whitneyRadius A κ x := by
  have hd : dist x y < whitneyRadius A κ x := by simpa [mem_ball, dist_comm] using hy
  have h1 := infDist_le_infDist_add_dist (x := x) (y := y) (s := Aᶜ)
  have h2 := infDist_le_infDist_add_dist (x := y) (y := x) (s := Aᶜ)
  rw [dist_comm y x] at h2
  constructor <;> linarith

end RothschildStein.H2
