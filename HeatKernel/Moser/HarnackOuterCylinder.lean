-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.BombieriGiustiCylinders
import Mathlib.Tactic

/-! # Containment in the outer Harnack cylinder

The iteration sets, logarithmic tail regions and comparison targets all lie in
the cylinder on which the local weak equation and nonnegativity are assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
namespace HeatKernel
variable {E : Type*} [PseudoMetricSpace E]

/-- The two outer iteration cylinders lie inside the domain of the equation. -/
theorem harnackIterationCylinders_subset_outer (x : E) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    harnackEarlierIterationCylinder x t r 1 ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) ∧
      harnackLaterIterationCylinder x t r 1 ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
  have hb : Metric.ball x (5 / 4 * r) ⊆ Metric.ball x (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  constructor
  · intro z hz
    dsimp only [harnackEarlierIterationCylinder] at hz
    simp only [one_pow, mul_one] at hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr],
      by nlinarith [hz.1.2, sq_pos_of_pos hr]⟩, hb hz.2⟩
  · intro z hz
    dsimp only [harnackLaterIterationCylinder] at hz
    simp only [one_pow, mul_one] at hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr], hz.1.2⟩, hb hz.2⟩

/-- Every permitted separating time places both logarithmic tail regions
inside the domain of the equation. -/
theorem harnackLogarithmicRegions_subset_outer (x : E) (t : ℝ) {r τ : ℝ}
    (hr : 0 < r) (hτlower : t - 113 / 64 * r ^ 2 < τ)
    (hτupper : τ < t - 111 / 64 * r ^ 2) :
    Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r) ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) ∧
      Ioo τ t ×ˢ Metric.ball x (5 / 4 * r) ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
  have hb : Metric.ball x (5 / 4 * r) ⊆ Metric.ball x (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  constructor
  · intro z hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr],
      by nlinarith [hz.1.2, sq_pos_of_pos hr]⟩, hb hz.2⟩
  · intro z hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr], hz.1.2⟩, hb hz.2⟩

/-- Both essential-extremum target sets lie in the outer cylinder. -/
theorem harnackTargetCylinders_subset_outer (x : E) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    harnackEarlierTargetCylinder x t r ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) ∧
      harnackLaterTargetCylinder x t r ⊆
        Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
  have hb : Metric.ball x r ⊆ Metric.ball x (2 * r) := Metric.ball_subset_ball (by linarith)
  constructor
  · intro z hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr],
      by nlinarith [hz.1.2, sq_pos_of_pos hr]⟩, hb hz.2⟩
  · intro z hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr], hz.1.2⟩, hb hz.2⟩

end HeatKernel
