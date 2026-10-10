-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MetricBallBoundary
public import HeatKernel.Poincare.WhitneyRadius
public import Mathlib.Tactic.FieldSimp

/-! Radius, center-distance, and shadow containment bounds along radial metric segments. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace HeatKernel

/-- A radius comparison and a center-distance bound place the entire starting ball
in a controlled dilation of a meeting ball. -/
theorem ball_subset_of_radius_and_center_bound {E : Type*} [PseudoMetricSpace E]
    {z w : E} {a b κ : ℝ} (hba : b ≤ 3 * a) (hd : dist z w ≤ (κ + 10) * a) :
    ball z b ⊆ ball w ((κ + 13) * a) := by
  intro y hy
  apply mem_ball.mpr
  calc
    dist y w ≤ dist y z + dist z w := dist_triangle y z w
    _ < b + (κ + 10) * a := add_lt_add_of_lt_of_le (mem_ball.mp hy) hd
    _ ≤ (κ + 13) * a := by linarith

/-- Every fivefold boundary-distance ball meeting a radial minimizing segment has
radius at least a third of the starting Whitney radius. Its center and dilation also
control the whole starting ball. -/
theorem boundaryBall_bounds_of_radial_segment_meeting {E : Type*} [MetricSpace E]
    {x z w : E} {r κ : ℝ} (hκ : 10 < κ) (hz : z ∈ ball x r)
    (hcompl : (ball x r)ᶜ.Nonempty) {γ : Icc (0 : ℝ) 1 → E}
    (hzero : γ ⟨0, by norm_num⟩ = z) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ s t, dist (γ s) (γ t) = dist z x * dist s t)
    (hmeet : (ball w (5 * (infDist w (ball x r)ᶜ / κ)) ∩ range γ).Nonempty) :
    (infDist z (ball x r)ᶜ / κ) / 3 ≤ infDist w (ball x r)ᶜ / κ ∧
      dist z w ≤ (κ + 10) * (infDist w (ball x r)ᶜ / κ) ∧
      ball z (infDist z (ball x r)ᶜ / κ) ⊆
        ball w ((κ + 13) * (infDist w (ball x r)ᶜ / κ)) := by
  have hk : 0 < κ := by linarith
  let δ := fun y : E => infDist y (ball x r)ᶜ
  let a := δ w / κ
  let b := δ z / κ
  have hw : δ w = κ * a := by dsimp only [a]; field_simp [hk.ne']
  have hz' : δ z = κ * b := by dsimp only [b]; field_simp [hk.ne']
  obtain ⟨v, hv, t, rfl⟩ := hmeet
  have ht := metric_segment_boundary_bounds hz hcompl hzero hone hγ t
  have hdist : dist (γ t) w ≤ 5 * a := (mem_ball.mp hv).le
  have hboundary : κ * b / 2 ≤ δ (γ t) := by rw [← hz']; exact ht.2.2
  have hthird : b / 3 ≤ a := radius_third_le_of_path_meeting
    (lipschitz_infDist_pt (ball x r)ᶜ) (div_nonneg infDist_nonneg hk.le)
    (by norm_num : (0 : ℝ) ≤ 5) (by linarith) hk hw hboundary hdist
  have hcenter : dist z w ≤ (κ + 10) * a := by
    have hh := dist_start_le_of_path_meeting (lipschitz_infDist_pt (ball x r)ᶜ)
      hw (le_rfl : dist z (γ t) ≤ dist z (γ t)) ht.2.1 hdist
    simpa only [show (κ + 2 * (5 : ℝ)) = κ + 10 by ring] using hh
  refine ⟨hthird, hcenter, ball_subset_of_radius_and_center_bound ?_ hcenter⟩
  linarith

end HeatKernel
