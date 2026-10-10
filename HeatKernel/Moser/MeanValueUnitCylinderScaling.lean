-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueWeakSolutionScaling
public import HeatKernel.Geometry.BallVolume
public import HeatKernel.Geometry.CoordinateBall
import Mathlib.Tactic

/-! # Scaling backward horizontal cylinders to the unit cylinder -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A weak solution on a backward horizontal cylinder becomes a weak solution on
the unit backward cylinder, with the literal pulled-back coefficient field. -/
theorem IsLocalWeakSolution.unit_cylinder_pullback {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a
      ⟨Ioo (t₀ - r ^ 2) t₀, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x₀ r,
        isOpen_horizontalBall G hq hqpos hspan x₀ r⟩ u) :
    let T := parabolicGroupHomeomorph G t₀ x₀ r hr
    IsLocalWeakSolution G hq hqpos hw hspan
      (fun t x i j => a (T (t, x)).1 (T (t, x)).2 i j)
      ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) 0 1,
        isOpen_horizontalBall G hq hqpos hspan 0 1⟩
      (fun t x => u (T (t, x)).1 (T (t, x)).2) := by
  apply IsLocalWeakSolution.parabolic_pullback G hq hqpos hw hspan a _ _ hu
    t₀ x₀ r hr
  · intro t ht
    change -1 < t ∧ t < 0 at ht
    change t₀ - r ^ 2 < t₀ + r ^ 2 * t ∧ t₀ + r ^ 2 * t < t₀
    constructor
    · nlinarith [mul_lt_mul_of_pos_left ht.1 (sq_pos_of_pos hr)]
    · nlinarith [mul_lt_mul_of_pos_left ht.2 (sq_pos_of_pos hr)]
  · intro x hx
    change G.mul x₀ (G.dilate r x) ∈ horizontalBall (G.horizontalFields hq) x₀ r
    rw [horizontalBall_eq_image_unitBall G hq hw hr x₀]
    exact ⟨x, hx, rfl⟩

end HeatKernel
