-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.BallMeasures

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Distance comparison away from a displaced centre (BB (7.8), p. 299). -/
theorem distance_comparison {x₀ x y : X} (h : 2 * dist x₀ x < dist x₀ y) :
    (2 / 3 : ℝ) * dist x y ≤ dist x₀ y ∧ dist x₀ y ≤ 2 * dist x y := by
  have h₁ := dist_triangle x x₀ y
  have h₂ := dist_triangle x₀ x y
  rw [dist_comm x x₀] at h₁
  constructor <;> linarith

/-- First comparison with two doublings, using only radii at most 6ρ. -/
theorem DoublingPatch.volume_compare_left (P : DoublingPatch X) {x₀ x y : X}
    (hx : x ∈ P.S) (h : 2 * dist x₀ x < dist x₀ y)
    (hκ : dist x₀ y ≤ 4 * P.ρ) :
    volumeAt P.μ x₀ y ≤ ENNReal.ofReal P.C_D ^ 2 * volumeAt P.μ x y := by
  have hp₀ : 0 < dist x₀ y := by have := dist_nonneg (x := x₀) (y := x); linarith
  have hp : 0 < dist x y := by
    have := (distance_comparison h).2; linarith
  have hsub : ball x₀ (dist x₀ y) ⊆ ball x ((3 / 2 : ℝ) * dist x₀ y) := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have := dist_triangle w x₀ x
    linarith
  refine (measure_mono hsub).trans (P.compare_pow hx hp (by positivity)
    (by linarith) 2 ?_)
  have := (distance_comparison h).2
  norm_num
  linarith

end RothschildStein.H2
