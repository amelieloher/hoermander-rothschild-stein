-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.NearbyChartInjectivity
public import RothschildStein.G4.WeightedCoefficientBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace RothschildStein.G4

/-- A nearby injective Euclidean coordinate ball contains one
uniform weighted chart box at every radius at most one. Reference-frame
suboptimality is subsequently preserved at its fixed radius (BB p. 453). -/
theorem exists_nearby_injective_weighted_boxes {P : Type*} [TopologicalSpace P] {n : ℕ}
    (w : Fin n → ℕ+) (f : P → (Fin n → ℝ) → (Fin n → ℝ)) (p₀ : P)
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hlocal : ∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p₀), DifferentiableAt ℝ (f q.2) q.1)
    (hder : ContinuousAt (fun q : (Fin n → ℝ) × P => fderiv ℝ (f q.2) q.1) (0, p₀))
    (hbase : fderiv ℝ (f p₀) 0 = (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ V : Set P, V ∈ 𝓝 p₀ ∧
      ∀ p ∈ V, ∀ r : ℝ, 0 < r → r ≤ 1 → InjOn (f p) (weightedBox w (a * r)) := by
  obtain ⟨ρ, hρ, V, hV, hinj⟩ :=
    exists_nearby_injective_ball_of_joint_derivative_continuity f 0 p₀ L hlocal hder hbase
  let a := min (1 : ℝ) (ρ / 2)
  have ha : 0 < a := lt_min zero_lt_one (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haρ : a ≤ ρ := (min_le_right _ _).trans (by linarith)
  refine ⟨a, ha, ha1, V, hV, ?_⟩
  intro p hp r hr hr1
  apply (hinj p hp).mono
  have har : a * r ≤ a := mul_le_of_le_one_right ha.le hr1
  exact (weightedBox_subset_ball w (mul_pos ha hr) (har.trans ha1)).trans
    (ball_subset_ball (har.trans haρ))

end RothschildStein.G4
